theory Finprod
  imports IDirProds
begin

lemma (in comm_group) finprod_subgroup:
  assumes "f \<in> S \<rightarrow> H" "subgroup H G"
  shows "finprod G f S = finprod (G\<lparr>carrier := H\<rparr>) f S"
proof (cases "finite S")
  case True
  interpret H: comm_group "G\<lparr>carrier := H\<rparr>" using subgroup_is_comm_group[OF assms(2)] .
  show ?thesis using True assms
  proof (induction S rule: finite_induct)
    case empty
    then show ?case using finprod_empty H.finprod_empty by simp
  next
    case i: (insert x F)
    then have "finprod G f F = finprod (G\<lparr>carrier := H\<rparr>) f F" by blast
    moreover have "finprod G f (insert x F) = f x \<otimes> finprod G f F"
    proof(intro finprod_insert[OF i(1, 2), of f])
      show "f \<in> F \<rightarrow> carrier G" "f x \<in> carrier G" using i(4) subgroup.subset[OF i(5)] by blast+
    qed
    ultimately have "finprod G f (insert x F) = f x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> finprod (G\<lparr>carrier := H\<rparr>) f F" by auto
    moreover have "finprod (G\<lparr>carrier := H\<rparr>) f (insert x F) = \<dots>"
    proof(intro H.finprod_insert[OF i(1, 2)])
      show "f \<in> F \<rightarrow> carrier (G\<lparr>carrier := H\<rparr>)" "f x \<in> carrier (G\<lparr>carrier := H\<rparr>)" using i(4) by auto
    qed
    ultimately show ?case by simp
  qed
next
  case False
  then show ?thesis unfolding finprod_def by simp
qed

lemma (in comm_group) finprod_eq:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<otimes> g a = h a"
  and "f \<in> A \<rightarrow> carrier G" "g \<in> A \<rightarrow> carrier G" "h \<in> A \<rightarrow> carrier G"
  shows "finprod G h A = finprod G f A \<otimes> finprod G g A" using assms
proof(induct A rule: infinite_finite_induct)
case (infinite A)
then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case i: (insert x F)
  then have iH: "finprod G h F = finprod G f F \<otimes> finprod G g F" by fast
  have f: "finprod G f (insert x F) = f x \<otimes> finprod G f F" by(intro finprod_insert[OF i(1, 2), of f]; use i(5) in simp)
  have g: "finprod G g (insert x F) = g x \<otimes> finprod G g F" by(intro finprod_insert[OF i(1, 2), of g]; use i(6) in simp)
  have h: "finprod G h (insert x F) = h x \<otimes> finprod G h F" by(intro finprod_insert[OF i(1, 2), of h]; use i(7) in simp)  
  also have "\<dots> = h x \<otimes> (finprod G f F \<otimes> finprod G g F)" using iH by argo
  also have "\<dots> = f x \<otimes> g x \<otimes> (finprod G f F \<otimes> finprod G g F)" using i(4) by simp
  also have "\<dots> = f x \<otimes> finprod G f F \<otimes> (g x \<otimes> finprod G g F)" using m_comm m_assoc i(5-7) by simp
  also have "\<dots> = finprod G f (insert x F) \<otimes> finprod G g (insert x F)" using f g by argo
  finally show ?case .
qed

lemma (in comm_group) finprod_closed_subgroup:
  assumes "subgroup H G" "f \<in> A \<rightarrow> H"
  shows "finprod G f A \<in> H"
  using assms(2)
proof (induct A rule: infinite_finite_induct)
case (infinite A)
then show ?case using subgroup.one_closed[OF assms(1)] by auto
next
  case empty
  then show ?case using subgroup.one_closed[OF assms(1)] by auto
next
  case i: (insert x F)
  from finprod_insert[OF i(1, 2), of f] i have fi: "finprod G f (insert x F) = f x \<otimes> finprod G f F"
    using subgroup.subset[OF assms(1)] by blast
  from i have "finprod G f F \<in> H" "f x \<in> H" by blast+
  with fi show ?case using subgroup.m_closed[OF assms(1)] by presburger 
qed

lemma (in comm_group) finprod_comp:
  assumes "inj_on g A" "(f \<circ> g) ` A \<subseteq> carrier G"
  shows "finprod G f (g ` A) = finprod G (f \<circ> g) A"
  using finprod_reindex[OF _ assms(1), of f] using assms(2) unfolding comp_def by blast

lemma (in comm_group) finprod_minus:
  assumes "a \<in> A" "f \<in> A \<rightarrow> carrier G" "finite A"
  shows "finprod G f A = f a \<otimes> finprod G f (A - {a})"
proof -
  from assms have "A = insert a (A - {a})" by blast
  then have "finprod G f A = finprod G f (insert a (A - {a}))" by simp
  also have "\<dots> = f a \<otimes> finprod G f (A - {a})" using assms by (intro finprod_insert, auto)
  finally show ?thesis .
qed

lemma (in comm_group) finprod_minus_symm:
  assumes "a \<in> A" "f \<in> A \<rightarrow> carrier G" "finite A"
  shows "finprod G f A = finprod G f (A - {a}) \<otimes> f a"
proof -
  from assms have "A = insert a (A - {a})" by blast
  then have "finprod G f A = finprod G f (insert a (A - {a}))" by simp
  also have "\<dots> = f a \<otimes> finprod G f (A - {a})" using assms by (intro finprod_insert, auto)
  also have "\<dots> = finprod G f (A - {a}) \<otimes> f a"
    by (intro m_comm, use assms in blast, intro finprod_closed, use assms in blast)
  finally show ?thesis .
qed

lemma (in comm_group) finprod_singleton:
  assumes "f x \<in> carrier G" "finprod G f {x} = a"
  shows "f x = a"
proof -
  have "finprod G f {x} = f x \<otimes> finprod G f {}" using finprod_minus[of x "{x}" f] assms by auto
  thus ?thesis using assms by simp
qed

lemma (in comm_group) finprod_exp:
  assumes "A \<subseteq> carrier G" "f \<in> A \<rightarrow> carrier G"
  shows "(finprod G f A) [^] (k::int) = finprod G ((\<lambda>a. a [^] k) \<circ> f) A"
  using assms
proof(induction A rule: infinite_finite_induct)
  case i: (insert x F)
  hence ih: "finprod G f F [^] k = finprod G ((\<lambda>a. a [^] k) \<circ> f) F" by blast
  have fpc: "finprod G f F \<in> carrier G" by (intro finprod_closed, use i in auto)
  have fxc: "f x \<in> carrier G" using i by auto
  have "finprod G f (insert x F) = f x \<otimes> finprod G f F" by (intro finprod_insert, use i in auto)
  hence "finprod G f (insert x F) [^] k = (f x \<otimes> finprod G f F) [^] k" by simp
  also have "\<dots> = f x [^] k \<otimes> finprod G f F [^] k" using fpc fxc int_pow_distrib by blast
  also have "\<dots> = ((\<lambda>a. a [^] k) \<circ> f) x \<otimes> finprod G ((\<lambda>a. a [^] k) \<circ> f) F" using ih by simp
  also have "\<dots> = finprod G ((\<lambda>a. a [^] k) \<circ> f) (insert x F)" by (intro finprod_insert[symmetric], use i in auto)
  finally show ?case .
qed auto


lemma (in comm_group) generate_eq_finprod_PiE_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})" (is "?g = ?fp")
proof
  show "?g \<subseteq> ?fp"
  proof
    fix x
    assume x: "x \<in> ?g"
    thus "x \<in> ?fp"
    proof (induction rule: generate.induct)
      case one
      show ?case
      proof
        let ?r = "restrict (\<lambda>_. \<one>) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one by auto
        show "\<one> = finprod G ?r gs" by(intro finprod_one_eqI[symmetric], simp)
      qed
    next
      case g: (incl g)
      show ?case
      proof
        let ?r = "restrict ((\<lambda>_. \<one>)(g := g)) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one generate.incl[of g "{g}" G] by fastforce
        show "g = finprod G ?r gs"
        proof -
          have "finprod G ?r gs = ?r g \<otimes> finprod G ?r (gs - {g})"
          proof -
            have "gs = insert g (gs - {g})" using g by fast
            then have "finprod G ?r gs = finprod G ?r (insert g (gs - {g}))" by simp
            also have "\<dots> = ?r g \<otimes> finprod G ?r (gs - {g})"
              by(rule finprod_insert, use assms g in auto)
            finally show ?thesis .
          qed
          moreover have "?r g = g" using g by simp
          moreover have "finprod G ?r (gs - {g}) = \<one>" by(rule finprod_one_eqI; use g in simp)
          ultimately show ?thesis using assms g by auto
        qed
      qed
    next
      case g: (inv g)
      show ?case
      proof
        let ?r = "restrict ((\<lambda>_. \<one>)(g := inv g)) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one generate.inv[of g "{g}" G] by fastforce
        show "inv g = finprod G ?r gs"
        proof -
          have "finprod G ?r gs = ?r g \<otimes> finprod G ?r (gs - {g})"
          proof -
            have "gs = insert g (gs - {g})" using g by fast
            then have "finprod G ?r gs = finprod G ?r (insert g (gs - {g}))" by simp
            also have "\<dots> = ?r g \<otimes> finprod G ?r (gs - {g})"
              by(rule finprod_insert, use assms g in auto)
            finally show ?thesis .
          qed
          moreover have "?r g = inv g" using g by simp
          moreover have "finprod G ?r (gs - {g}) = \<one>" by(rule finprod_one_eqI; use g in simp)
          ultimately show ?thesis using assms g by auto
        qed
      qed
    next
      case gh: (eng g h)
      from gh obtain i where i: "i \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" "g = finprod G i gs" by blast
      from gh obtain j where j: "j \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" "h = finprod G j gs" by blast
      from i j have "g \<otimes> h = finprod G i gs \<otimes> finprod G j gs" by blast
      also have "\<dots> = finprod G (\<lambda>a. i a \<otimes> j a) gs"
      proof(intro finprod_multf[symmetric]; rule)
        fix x
        assume x: "x \<in> gs"
        have "i x \<in> generate G {x}" "j x \<in> generate G {x}"using i(1) j(1) x by blast+
        thus "i x \<in> carrier G" "j x \<in> carrier G" using generate_incl[of "{x}"] x assms(2) by blast+
      qed
      also have "\<dots> = finprod G (restrict (\<lambda>a. i a \<otimes> j a) gs) gs"
      proof(intro finprod_cong)
        have ip: "i g \<in> generate G {g}" if "g \<in> gs" for g using i that by auto
        have jp: "j g \<in> generate G {g}" if "g \<in> gs" for g using j that by auto
        have "i g \<otimes> j g \<in> generate G {g}" if "g \<in> gs" for g using generate.eng[OF ip[OF that] jp[OF that]] .
        thus "((\<lambda>a. i a \<otimes> j a) \<in> gs \<rightarrow> carrier G) = True" using generate_incl assms(2) by blast
      qed auto
      finally have "g \<otimes> h = finprod G (restrict (\<lambda>a. i a \<otimes> j a) gs) gs" .
      moreover have "(restrict (\<lambda>a. i a \<otimes> j a) gs) \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})"
      proof -
        have ip: "i g \<in> generate G {g}" if "g \<in> gs" for g using i that by auto
        have jp: "j g \<in> generate G {g}" if "g \<in> gs" for g using j that by auto
        have "i g \<otimes> j g \<in> generate G {g}" if "g \<in> gs" for g using generate.eng[OF ip[OF that] jp[OF that]] .
        thus ?thesis by auto
      qed
      ultimately show ?case using i j by blast
    qed
  qed
  show "?fp \<subseteq> ?g"
  proof
    fix x
    assume x: "x \<in> ?fp"
    then obtain f where f: "f \<in> (Pi\<^sub>E gs (\<lambda>a. generate G {a}))" "x = finprod G f gs" by blast
    have sg: "subgroup ?g G" by(intro generate_is_subgroup, fact)
    have "finprod G f gs \<in> ?g"
    proof(intro finprod_closed_subgroup[OF sg])
      have "f g \<in> generate G gs" if "g \<in> gs" for g
      proof -
        have "f g \<in> generate G {g}" using f(1) that by auto
        moreover have "generate G {g} \<subseteq> generate G gs" by(intro mono_generate, use that in simp)
        ultimately show ?thesis by fast
      qed
      thus "f \<in> gs \<rightarrow> generate G gs" by simp
    qed
    thus "x \<in> ?g" using f by blast
  qed
qed

lemma (in comm_group) generate_eq_finprod_Pi_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})" (is "?g = ?fp")
proof -
  have "(\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a}) = (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})"
  proof
    have "Pi\<^sub>E gs (\<lambda>a. generate G {a}) \<subseteq> Pi gs (\<lambda>a. generate G {a})" by blast
    thus "(\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a}) \<subseteq> (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})" by blast
    show "(\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a}) \<subseteq> (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})"
    proof
      fix x
      assume x: "x \<in> (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})"
      then obtain f where f: "x = finprod G f gs" "f \<in> Pi gs (\<lambda>a. generate G {a})" by blast
      moreover have "finprod G f gs = finprod G (restrict f gs) gs"
      proof(intro finprod_cong)
        have "f g \<in> carrier G" if "g \<in> gs" for g
          using that f(2) mono_generate[of "{g}" gs] generate_incl[OF assms(2)] by fast
        thus "(f \<in> gs \<rightarrow> carrier G) = True" by blast
      qed auto        
      moreover have "restrict f gs \<in> Pi\<^sub>E gs (\<lambda>a. generate G {a})" using f(2) by simp
      ultimately show "x \<in> (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})" by blast
    qed
  qed
  with generate_eq_finprod_PiE_image[OF assms] show ?thesis by auto
qed

lemma (in comm_group) generate_eq_finprod_Pi_int_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` Pi gs (\<lambda>_. (UNIV::int set))"
proof -
  from generate_eq_finprod_Pi_image[OF assms] have "generate G gs = (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})" .
  also have "\<dots> = (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` Pi gs (\<lambda>_. (UNIV::int set))"
  proof(rule; rule)
    fix x
    assume x: "x \<in> (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})"
    then obtain f where f: "f \<in> (\<Pi> a\<in>gs. generate G {a})" "x = finprod G f gs" by blast
    hence "\<exists>k::int. f a = a [^] k" if "a \<in> gs" for a using generate_pow[of a] that assms(2) by blast
    hence "\<exists>(h::'a \<Rightarrow> int). \<forall>a\<in>gs. f a = a [^] h a" by meson
    then obtain h where h: "\<forall>a\<in>gs. f a = a [^] h a" "h \<in> gs \<rightarrow> (UNIV :: int set)" by auto
    have "finprod G (\<lambda>g. g [^] h g) gs = finprod G f gs" by (intro finprod_cong, use int_pow_closed h assms(2) in auto)
    with f have "x = finprod G (\<lambda>g. g [^] h g) gs" by argo
    with h(2) show "x \<in> (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` (gs \<rightarrow> (UNIV::int set))" by auto
  next
    fix x
    assume x: "x \<in> (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` (gs \<rightarrow> (UNIV::int set))"
    then obtain h where h: "x = finprod G (\<lambda>g. g [^] h g) gs" "h \<in> gs \<rightarrow> (UNIV :: int set)" by blast
    hence "\<exists>k\<in>generate G {a}. a [^] h a = k" if "a \<in> gs" for a using generate_pow[of a] that assms(2) by blast
    then obtain f where f: "\<forall>a\<in>gs. a [^] h a = f a" "f \<in> (\<Pi> a\<in>gs. generate G {a})" by fast
    have "finprod G f gs = finprod G (\<lambda>g. g [^] h g) gs"
    proof(intro finprod_cong)
      have "f a \<in> carrier G" if "a \<in> gs" for a using generate_incl[of "{a}"] assms(2) that f(2) by fast
      thus "(f \<in> gs \<rightarrow> carrier G) = True" by blast
    qed (use f in auto)
    with h have "x = finprod G f gs" by argo
    with f(2) show "x \<in> (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})" by blast
  qed
  finally show ?thesis .
qed

lemma (in comm_group) generate_one_switched_exp_eqI:
  assumes "A \<subseteq> carrier G" "a \<in> A" "B = (A - {a}) \<union> {b}"
  and "f \<in> A \<rightarrow> (UNIV::int set)" "g \<in> B \<rightarrow> (UNIV::int set)"
  and "a = finprod G (\<lambda>x. x [^] g x) B" "b = finprod G (\<lambda>x. x [^] f x) A"
  shows "generate G A = generate G B"
proof(intro generate_one_switched_eqI[OF assms(1, 2, 3)]; cases "finite A")
  case True
  hence fB: "finite B" using assms(3) by blast
  have cB: "B \<subseteq> carrier G"
  proof -
    have "b \<in> carrier G" by (subst assms(7), intro finprod_closed, use assms(1, 4) int_pow_closed in fast)
    thus ?thesis using assms(1, 3) by blast
  qed
  show "a \<in> generate G B"
  proof(subst generate_eq_finprod_Pi_image[OF fB cB], rule)
    show "a = finprod G (\<lambda>x. x [^] g x) B" by fact
    have "x [^] g x \<in> generate G {x}" if "x \<in> B" for x using generate_pow[of x] cB that by blast
    thus "(\<lambda>x. x [^] g x) \<in> (\<Pi> a\<in>B. generate G {a})" unfolding Pi_def by blast
  qed
  show "b \<in> generate G A"
  proof(subst generate_eq_finprod_Pi_image[OF True assms(1)], rule)
    show "b = finprod G (\<lambda>x. x [^] f x) A" by fact
    have "x [^] f x \<in> generate G {x}" if "x \<in> A" for x using generate_pow[of x] assms(1) that by blast
    thus "(\<lambda>x. x [^] f x) \<in> (\<Pi> a\<in>A. generate G {a})" unfolding Pi_def by blast
  qed
next
  case False
  hence b: "b = \<one>" using assms(7) unfolding finprod_def by simp
  from False assms(3) have "infinite B" by simp
  hence a: "a = \<one>" using assms(6) unfolding finprod_def by simp
  show "a \<in> generate G B" using generate.one a by blast
  show "b \<in> generate G A" using generate.one b by blast
qed

lemma (in comm_group) IDirProds_eq_finprod_PiE:
  assumes "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  shows "IDirProds G Hs = (\<lambda>x. finprod G x Hs) ` (Pi\<^sub>E Hs id)" (is "?DP = ?fp")
proof
  show "?fp \<subseteq> ?DP"
  proof
    fix x
    assume x: "x \<in> ?fp"
    then obtain f where f: "f \<in> (Pi\<^sub>E Hs id)" "x = finprod G f Hs" by blast
    have sDP: "subgroup ?DP G" by(intro IDirProds_is_subgroup; use subgroup.subset[OF assms(2)] in blast)
    have "finprod G f Hs \<in> ?DP"
    proof(intro finprod_closed_subgroup[OF sDP])
      have "f H \<in> IDirProds G Hs" if "H \<in> Hs" for H
      proof
        show "f H \<in> H" using f(1) that by auto
        show "H \<subseteq> IDirProds G Hs" by(intro IDirProds_incl[OF that])
      qed
      thus "f \<in> Hs \<rightarrow> IDirProds G Hs" by simp
    qed
    thus "x \<in> ?DP" using f by blast
  qed
  show "?DP \<subseteq> ?fp"
  proof(unfold IDirProds_def; rule subsetI)
    fix x
    assume x: "x \<in> generate G (\<Union>Hs)"
    thus "x \<in> ?fp" using assms
    proof (induction rule: generate.induct)
      case one
      define g where g: "g = (\<lambda>x. if x \<in> Hs then \<one> else undefined)"
      then have "g \<in> Pi\<^sub>E Hs id"
        using subgroup.one_closed[OF one(2)] by auto
      moreover have "finprod G g Hs = \<one>" by(intro finprod_one_eqI; use g in simp)
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case i: (incl h)
      from i obtain H where H: "H \<in> Hs" "h \<in> H" by blast
      define hf where "hf = (\<lambda>x. (if x \<in> Hs then \<one> else undefined))(H := h)"
      with H have "hf \<in> Pi\<^sub>E Hs id"
        using subgroup.one_closed[OF i(3)] by force
      moreover have "finprod G hf Hs = h"
      proof -
        have "finprod G hf Hs = hf H \<otimes> finprod G hf (Hs - {H})"
        proof -
          have "Hs = insert H (Hs - {H})" using H by fast
          then have "finprod G hf Hs = finprod G hf (insert H (Hs - {H}))" by simp
          also have "\<dots> = hf H \<otimes> finprod G hf (Hs - {H})"
            by (rule finprod_insert; use assms hf_def subgroup.subset[OF i(3)[OF H(1)]] H in auto)
          finally show ?thesis .
        qed
        moreover have "hf H = h" using hf_def by simp
        moreover have "finprod G hf (Hs - {H}) = \<one>" by(rule finprod_one_eqI; use hf_def in simp)
        ultimately show ?thesis using subgroup.subset[OF i(3)[OF H(1)]] H(2) by auto
      qed
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case i: (inv h)
      from i obtain H where H: "H \<in> Hs" "h \<in> H" by blast
      have ih: "inv h \<in> H" using subgroup.m_inv_closed[OF i(3)[OF H(1)] H(2)] .
      define hf where "hf = (\<lambda>x. (if x \<in> Hs then \<one> else undefined))(H := inv h)"
      with H ih have "hf \<in> Pi\<^sub>E Hs id"
        using subgroup.one_closed[OF i(3)] by force
      moreover have "finprod G hf Hs = inv h"
      proof -
        have "finprod G hf Hs = hf H \<otimes> finprod G hf (Hs - {H})"
        proof -
          have "Hs = insert H (Hs - {H})" using H by fast
          then have "finprod G hf Hs = finprod G hf (insert H (Hs - {H}))" by simp
          also have "\<dots> = hf H \<otimes> finprod G hf (Hs - {H})"
            by (rule finprod_insert; use assms hf_def subgroup.subset[OF i(3)[OF H(1)]] H in auto)
          finally show ?thesis .
        qed
        moreover have "hf H = inv h" using hf_def by simp
        moreover have "finprod G hf (Hs - {H}) = \<one>" by(rule finprod_one_eqI; use hf_def in simp)
        ultimately show ?thesis using subgroup.subset[OF i(3)[OF H(1)]] H(2) by auto
      qed
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case e: (eng a b)
      from e obtain f where f: "f \<in> Pi\<^sub>E Hs id" "a = finprod G f Hs" by blast
      from e obtain g where g: "g \<in> Pi\<^sub>E Hs id" "b = finprod G g Hs" by blast
      from f g have "a \<otimes> b = finprod G f Hs \<otimes> finprod G g Hs" by blast
      also have "\<dots> = finprod G (\<lambda>a. f a \<otimes> g a) Hs"
      proof(intro finprod_multf[symmetric])
        have "\<Union>Hs \<subseteq> carrier G" using subgroup.subset[OF e(6)] by blast
        thus "f \<in> Hs \<rightarrow> carrier G" "g \<in> Hs \<rightarrow> carrier G"
          using f(1) g(1) unfolding PiE_def Pi_def by auto
      qed
      also have "\<dots> = finprod G (restrict (\<lambda>a. f a \<otimes> g a) Hs) Hs"
      proof(intro finprod_cong)
        show "Hs = Hs" by simp
        show "\<And>i. i \<in> Hs =simp=> f i \<otimes> g i = (\<lambda>a\<in>Hs. f a \<otimes> g a) i" by simp
        have fp: "f H \<in> H" if "H \<in> Hs" for H using f that by auto
        have gp: "g H \<in> H" if "H \<in> Hs" for H using g that by auto
        have "f H \<otimes> g H \<in> H" if "H \<in> Hs" for H using subgroup.m_closed[OF e(6)[OF that] fp[OF that] gp[OF that]] .
        thus "((\<lambda>a. f a \<otimes> g a) \<in> Hs \<rightarrow> carrier G) = True" using subgroup.subset[OF e(6)] by auto
      qed
      finally have "a \<otimes> b = finprod G (restrict (\<lambda>a. f a \<otimes> g a) Hs) Hs" .
      moreover have "(restrict (\<lambda>a. f a \<otimes> g a) Hs) \<in> Pi\<^sub>E Hs id"
      proof -
        have fp: "f H \<in> H" if "H \<in> Hs" for H using f that by auto
        have gp: "g H \<in> H" if "H \<in> Hs" for H using g that by auto
        have "f H \<otimes> g H \<in> H" if "H \<in> Hs" for H using subgroup.m_closed[OF e(6)[OF that] fp[OF that] gp[OF that]] .
        thus ?thesis by auto
      qed
      ultimately show ?case using f g by blast
    qed
  qed
qed

lemma (in comm_group) IDirProds_eq_finprod_Pi:
  assumes "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  shows "IDirProds G Hs = (\<lambda>x. finprod G x Hs) ` (Pi Hs id)" (is "?DP = ?fp")
proof -
  have "(\<lambda>x. finprod G x Hs) ` (Pi Hs id) = (\<lambda>x. finprod G x Hs) ` (Pi\<^sub>E Hs id)"
  proof
    have "Pi\<^sub>E Hs id \<subseteq> Pi Hs id" by blast
    thus "(\<lambda>x. finprod G x Hs) ` Pi\<^sub>E Hs id \<subseteq> (\<lambda>x. finprod G x Hs) ` Pi Hs id" by blast
    show "(\<lambda>x. finprod G x Hs) ` Pi Hs id \<subseteq> (\<lambda>x. finprod G x Hs) ` Pi\<^sub>E Hs id"
    proof
      fix x
      assume x: "x \<in> (\<lambda>x. finprod G x Hs) ` Pi Hs id"
      then obtain f where f: "x = finprod G f Hs" "f \<in> Pi Hs id" by blast
      moreover have "finprod G f Hs = finprod G (restrict f Hs) Hs" by(intro finprod_cong; use f(2) subgroup.subset[OF assms(2)] in fastforce)
      moreover have "restrict f Hs \<in> Pi\<^sub>E Hs id" using f(2) by simp
      ultimately show "x \<in> (\<lambda>x. finprod G x Hs) ` Pi\<^sub>E Hs id" by blast
    qed
  qed
  with IDirProds_eq_finprod_PiE[OF assms] show ?thesis by auto
qed

lemma (in comm_group) comp_fam_imp_triv_finprod:
  assumes "complementary_family Hs" "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  and "finprod G f Hs = \<one>" "f \<in> Pi Hs id"
  shows "\<forall>H\<in>Hs. f H = \<one>"
proof (rule ccontr; clarify)
  from assms(5) have f: "f H \<in> H" if "H \<in> Hs" for H using that by fastforce
  fix H
  assume H: "H \<in> Hs"
  have sH: "subgroup H G" using assms(3)[OF H] .
  consider (triv) "H = {\<one>}" | (not_triv) "H \<noteq> {\<one>}" by blast
  thus "f H = \<one>"
  proof (cases)
    case triv
    then show ?thesis using f[OF H] by blast
  next
    case not_triv
    show ?thesis
    proof (rule ccontr)
      have fc: "f H \<in> carrier G" using f[OF H] subgroup.subset[OF sH] by blast
      assume no: "f H \<noteq> \<one>"
      have fH: "f H \<in> H" using f[OF H] .
      from subgroup.m_inv_closed[OF sH this] have ifH: "inv (f H) \<in> H" .
      moreover have "inv (f H) \<noteq> \<one>" using no fc by simp
      moreover have "inv (f H) = finprod G f (Hs - {H})"
      proof -
        have "\<one> = finprod G f Hs" using assms(4) by simp
        also have "\<dots> = finprod G f (insert H (Hs - {H}))"
        proof -
          have "Hs = insert H (Hs - {H})" using H by fast
          thus ?thesis by simp
        qed
        also have "\<dots> = f H \<otimes> finprod G f (Hs - {H})"
        proof(intro finprod_insert)
          show "finite (Hs - {H})" using assms(2) by blast
          show "H \<notin> Hs - {H}" by blast
          show "f \<in> Hs - {H} \<rightarrow> carrier G" using assms(3) f subgroup.subset by blast
          show "f H \<in> carrier G" by fact
        qed
        finally have o: "\<one> = f H \<otimes> finprod G f (Hs - {H})" .
        show ?thesis
        proof(intro inv_equality)
          show "f H \<in> carrier G" by fact
          show "finprod G f (Hs - {H}) \<in> carrier G"
            by (intro finprod_closed; use assms(3) f subgroup.subset in blast)
          from m_comm[OF this fc] o show "finprod G f (Hs - {H}) \<otimes> f H = \<one>" by simp
        qed
      qed
      moreover have "finprod G f (Hs - {H}) \<in> IDirProds G (Hs - {H})"
      proof (intro finprod_closed_subgroup IDirProds_is_subgroup)
        show "\<Union> (Hs - {H}) \<subseteq> carrier G" using assms(3) subgroup.subset by auto
        have "f J \<in> (IDirProds G (Hs - {H}))" if "J \<in> (Hs - {H})" for J
          using IDirProds_incl[OF that] f that by blast
        thus "f \<in> Hs - {H} \<rightarrow> IDirProds G (Hs - {H})" by blast
      qed
      ultimately have "\<not>complementary H (IDirProds G (Hs - {H}))"
        unfolding complementary_def by auto
      thus False using assms(1) H unfolding complementary_family_def by blast
    qed
  qed
qed

lemma (in comm_group) triv_finprod_imp_comp_fam:
  assumes "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  and "\<forall>f \<in> Pi Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>)"
shows "complementary_family Hs"
proof (unfold complementary_family_def; rule)
  fix H
  assume H: "H \<in> Hs"
  let ?DP = "IDirProds G (Hs - {H})"
  show "complementary H ?DP"
  proof (rule ccontr; unfold complementary_def)
    have sH: "subgroup H G" using assms(2)[OF H] .
    have sDP: "subgroup ?DP G"
      by (intro IDirProds_is_subgroup; use subgroup.subset[OF assms(2)] in blast)
    assume a: "H \<inter> IDirProds G (Hs - {H}) \<noteq> {\<one>}"
    then obtain x where x: "x \<in> H" "x \<in> IDirProds G (Hs - {H})" "x \<noteq> \<one>" using subgroup.one_closed sH sDP by blast
    then have "x \<in> (\<lambda>x. finprod G x (Hs - {H})) ` (Pi (Hs - {H}) id)" using IDirProds_eq_finprod_Pi[of "(Hs - {H})"] assms(1, 2) by blast
    then obtain ht where ht: "finprod G ht (Hs - {H}) = x" "ht \<in> Pi (Hs - {H}) id" by blast
    define h where h: "h = (ht(H := inv x))"
    then have hPi: "h \<in> Pi Hs id" using ht subgroup.m_inv_closed[OF assms(2)[OF H] x(1)] by auto
    have "finprod G h (Hs - {H}) = x"
    proof (subst ht(1)[symmetric], intro finprod_cong)
      show "Hs - {H} = Hs - {H}" by simp
      show "(h \<in> Hs - {H} \<rightarrow> carrier G) = True" using h ht(2) subgroup.subset[OF assms(2)]
        unfolding Pi_def id_def by auto
      show "\<And>i. i \<in> Hs - {H} =simp=> h i = ht i" using ht(2) h by simp
    qed
    moreover have "finprod G h Hs = h H \<otimes> finprod G h (Hs - {H})"
    proof -
      have "Hs = insert H (Hs - {H})" using H by fast
      then have "finprod G h Hs = finprod G h (insert H (Hs - {H}))" by simp
      also have "\<dots> = h H \<otimes> finprod G h (Hs - {H})"
      proof(intro finprod_insert)
        show "finite (Hs - {H})" "H \<notin> Hs - {H}" using assms(1) by blast+
        have "h J \<in> J" if "J \<in> Hs" for J using hPi that by auto
        thus "h H \<in> carrier G" "h \<in> Hs - {H} \<rightarrow> carrier G" using H subgroup.subset[OF assms(2)] by blast+
      qed
      finally show ?thesis .
    qed
    ultimately have "finprod G h Hs = inv x \<otimes> x" using h by simp
    then have "finprod G h Hs = \<one>" using subgroup.subset[OF sH] x(1) by auto
    moreover have "h H \<noteq> \<one>" using h x(3) subgroup.subset[OF sH] x(1) by force
    ultimately show False using assms(3) H hPi by blast
  qed
qed

lemma (in comm_group) triv_finprod_iff_comp_fam_Pi:
  assumes "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  shows "complementary_family Hs \<longleftrightarrow> (\<forall>f \<in> Pi Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>))"
  using comp_fam_imp_triv_finprod triv_finprod_imp_comp_fam assms by blast

lemma (in comm_group) triv_finprod_iff_comp_fam_PiE:
  assumes "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G"
  shows "complementary_family Hs \<longleftrightarrow> (\<forall>f \<in> Pi\<^sub>E Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>))"
proof
  show "complementary_family Hs \<Longrightarrow> \<forall>f\<in>Pi\<^sub>E Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>)" using triv_finprod_iff_comp_fam_Pi[OF assms] by blast
  have "\<forall>f\<in>Pi\<^sub>E Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>) \<Longrightarrow> \<forall>f\<in>Pi Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>)"
  proof(rule+)
    fix f H
    assume f: "f \<in> Pi Hs id" "finprod G f Hs = \<one>" and H: "H \<in> Hs"
    assume allf: "\<forall>f\<in>Pi\<^sub>E Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>)"
    have "f H = restrict f Hs H" using H by simp
    moreover have "finprod G (restrict f Hs) Hs = finprod G f Hs"
      using f subgroup.subset[OF assms(2)] unfolding Pi_def by(intro finprod_cong; auto)
    moreover have "restrict f Hs \<in> Pi\<^sub>E Hs id" using f by simp
    ultimately show "f H = \<one>" using allf f H by metis
  qed
  thus "\<forall>f\<in>Pi\<^sub>E Hs id. finprod G f Hs = \<one> \<longrightarrow> (\<forall>H\<in>Hs. f H = \<one>) \<Longrightarrow> complementary_family Hs" using triv_finprod_iff_comp_fam_Pi[OF assms] by blast
qed

lemma (in comm_group) triv_finprod_iff_comp_gens:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "(\<forall>f \<in> Pi\<^sub>E gs (\<lambda>a. generate G {a}). finprod G f gs = \<one> \<longrightarrow> (\<forall>a\<in>gs. f a = \<one>)) \<longleftrightarrow> compl_gens gs"
proof
  assume a: "\<forall>f\<in>\<Pi>\<^sub>E a\<in>gs. generate G {a}. finprod G f gs = \<one> \<longrightarrow> (\<forall>a\<in>gs. f a = \<one>)"
  show "compl_gens gs"
  proof (unfold compl_gens_def, rule)
    fix g
    assume g: "g \<in> gs"
    show "complementary (generate G {g}) (generate G (gs - {g}))" (is "complementary ?gg ?ggs")
    proof (rule ccontr, unfold complementary_def)
      from assms g have s: "subgroup ?gg G" "subgroup ?ggs G"
        by (intro generate_is_subgroup, auto, intro generate_is_subgroup, auto)
      assume nt: "?gg \<inter> ?ggs \<noteq> {\<one>}"
      with s obtain e where e: "e \<in> ?gg" "e \<in> ?ggs" "e \<noteq> \<one>" using subgroup.one_closed by blast
      then have ec: "e \<in> carrier G" using subgroup.subset s by blast
      then have ie: "inv e \<in> ?gg" "inv e \<in> ?ggs" using subgroup.m_inv_closed s e by fast+
      with assms generate_eq_finprod_PiE_image[of "gs - {g}"] obtain f where
        f: "finprod G f (gs - {g}) = inv e" "f \<in> (\<Pi>\<^sub>E a\<in>gs - {g}. generate G {a})" by fastforce
      let ?r = "f(g := e)"
      have rc: "f(g := e) \<in> gs \<rightarrow> carrier G"
      proof
        fix x
        assume x: "x \<in> gs"
        then have "?r x \<in> generate G {x}" using f(2) e(1) by(cases "x = g", auto)
        with generate_incl[OF assms(2)] mono_generate[of "{x}" gs] x show "?r x \<in> carrier G" by blast
      qed
      then have fc: "f \<in> (gs - {g}) \<rightarrow> carrier G" using g f by force
      have "finprod G ?r gs = \<one>"
      proof -
        have "finprod G ?r gs = ?r g \<otimes> finprod G ?r (gs - {g})" by (intro finprod_minus[OF g rc assms(1)])
        moreover have "?r g = e" by simp
        moreover have "finprod G ?r (gs - {g}) = inv e"
        proof -
          have "finprod G ?r (gs - {g}) = finprod G f (gs - {g})" by (intro finprod_cong, use rc assms fc in auto)
          thus ?thesis using f by simp
        qed
        ultimately show ?thesis using ec by fastforce
      qed
      moreover have "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using f g e by fastforce
      ultimately show False using a e g by fastforce
    qed
  qed
next
  assume c: "compl_gens gs"
  show "\<forall>f\<in>\<Pi>\<^sub>E a\<in>gs. generate G {a}. finprod G f gs = \<one> \<longrightarrow> (\<forall>a\<in>gs. f a = \<one>)"
  proof(rule, rule, rule, rule ccontr)
    fix f g
    assume f: "f \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" "finprod G f gs = \<one>"
    have fc: "f \<in> gs \<rightarrow> carrier G"
    proof
      fix x
      assume x: "x \<in> gs"
      then have "f x \<in> generate G {x}" using f(1) by fast
      with mono_generate[of "{x}" gs] generate_incl[OF assms(2)] x show "f x \<in> carrier G" by fast
    qed
    assume g: "g \<in> gs" "f g \<noteq> \<one>"
    with f have no: "generate G {g} \<noteq> {\<one>}" by blast
    with g f obtain e where e: "e \<in> generate G {g}" "e \<noteq> \<one>" "e = f g" using generate.one by blast
    then have ec: "e \<in> carrier G" using g assms(2) generate_incl by blast
    from subgroup.m_inv_closed[OF generate_is_subgroup e(1)] g(1) assms(2) e ec
    have ie: "inv e \<in> generate G {g}" "inv e \<noteq> \<one>" by auto
    let ?r = "restrict f (gs - {g})"
    have rr: "?r \<in> (\<Pi>\<^sub>E a\<in>gs - {g}. generate G {a})" using g f by auto
    have "inv e = finprod G ?r (gs - {g})"
    proof(intro inv_equality[OF _ ec])
      have "finprod G ?r (gs - {g}) = finprod G f (gs - {g})" by (intro finprod_cong; use fc in auto)
      moreover have "finprod G f gs = finprod G f (gs - {g}) \<otimes> f g" by (rule finprod_minus_symm[OF g(1) fc assms(1)])
      ultimately show "finprod G ?r (gs - {g}) \<otimes> e = \<one>" using f(2) e(3) by argo
      show "finprod G ?r (gs - {g}) \<in> carrier G" by (intro finprod_closed, use fc in blast)
    qed
    with generate_eq_finprod_PiE_image[of "gs - {g}"] assms rr have "inv e \<in> generate G (gs - {g})" by blast
    with ie have "\<not>complementary (generate G {g}) (generate G (gs - {g}))" unfolding complementary_def by blast
    with c g(1) show False unfolding compl_gens_def by blast
  qed
qed

(* belongs to IDirProd, but uses Finprod stuff *)
lemma (in comm_group) idirgen_ind:
  assumes "finite gs" "gs \<subseteq> carrier G" "g \<in> carrier G"
  and "is_idirgen (generate G gs) gs" "complementary (generate G {g}) (generate G gs)"
  shows "is_idirgen (generate G (gs \<union> {g})) (gs \<union> {g})"
proof(cases "g \<in> gs")
  case True
  hence "gs = (gs \<union> {g})" by blast
  thus ?thesis using assms(4) by auto 
next
  case gngs: False
  show ?thesis
  proof
    have gsgc: "gs \<union> {g} \<subseteq> carrier G" using assms(2, 3) by blast
    have figsg: "finite (gs \<union> {g})" using assms(1) by blast
    have sg: "subgroup (generate G {g}) G" by (intro generate_is_subgroup, use assms(3) in blast)
    from assms(4) is_idirgen.simps[of "generate G gs" gs] have ih: "\<forall>x. x \<in> gs \<longrightarrow> generate G {x} \<lhd> G" "compl_gens gs" by blast+
    hence ca: "\<forall>a\<in>gs. complementary (generate G {a}) (generate G (gs - {a}))" unfolding compl_gens_def by blast
    show "\<And>ga. ga \<in> gs \<union> {g} \<Longrightarrow> generate G {ga} \<lhd> G" using subgroup_imp_normal[OF sg] ih(1) by blast
    show "compl_gens (gs \<union> {g})" unfolding compl_gens_def
    proof(rule, rule ccontr)
      fix h
      assume h: "h \<in> gs \<union> {g}"
      assume c: "\<not> complementary (generate G {h}) (generate G (gs \<union> {g} - {h}))"
      show "False"
      proof (cases "h = g")
        case True
        with c have "\<not> complementary (generate G {g}) (generate G (gs - {g}))" by auto
        moreover have "complementary (generate G {g}) (generate G (gs - {g}))"
          by (rule subgroup_subset_complementary[OF generate_is_subgroup generate_is_subgroup[of gs] generate_is_subgroup mono_generate], use assms(2, 3, 5) in auto)
        ultimately show False by blast
      next
        case hng: False
        hence h: "h \<in> gs" "h \<noteq> g" using h by blast+
        hence "gs \<union> {g} - {h} = gs - {h} \<union> {g}" by blast
        with c have c: "\<not> complementary (generate G {h}) (generate G (gs - {h} \<union> {g}))" by argo
        then obtain k where k: "k \<in> generate G {h}" "k \<in> generate G (gs - {h} \<union> {g})" "k \<noteq> \<one>"
          unfolding complementary_def using generate.one by blast 
        with ca have kngh: "k \<notin> generate G (gs - {h})" using h unfolding complementary_def by blast
        from k(2) generate_eq_finprod_PiE_image[of "gs - {h} \<union> {g}"] assms(1) gsgc
        obtain f where f: "k = finprod G f (gs - {h} \<union> {g})" "f \<in> (\<Pi>\<^sub>E a\<in>gs - {h} \<union> {g}. generate G {a})"
          by blast
        have fg: "f a \<in> generate G {a}" if "a \<in> (gs - {h} \<union> {g})" for a using that f(2) by blast
        have fc: "f a \<in> carrier G" if "a \<in> (gs - {h} \<union> {g})" for a
        proof -
          have "generate G {a} \<subseteq> carrier G" if "a \<in> (gs - {h} \<union> {g})" for a
            using that generate_incl[of "{a}"] gsgc by blast
          thus "f a \<in> carrier G" using that fg by auto
        qed
        have kp: "k = f g \<otimes> finprod G f (gs - {h})"
        proof -
          have "(gs - {h} \<union> {g}) = insert g (gs - {h})" by fast
          moreover have "finprod G f (insert g (gs - {h})) = f g \<otimes> finprod G f (gs - {h})"
            by (intro finprod_insert, use fc assms(1) gngs in auto)
          ultimately show ?thesis using f(1) by argo
        qed
        have fgsh: "finprod G f (gs - {h}) \<in> generate G (gs - {h})"
        proof(intro finprod_closed_subgroup[OF generate_is_subgroup])
          show "gs - {h} \<subseteq> carrier G" using gsgc by blast
          have "f a \<in> generate G (gs - {h})" if "a \<in> (gs - {h})" for a
            using mono_generate[of "{a}" "gs - {h}"] fg that by blast
          thus "f \<in> gs - {h} \<rightarrow> generate G (gs - {h})" by blast
        qed
        have "f g \<otimes> finprod G f (gs - {h}) \<notin> generate G gs"
        proof
          assume fpgs: "f g \<otimes> finprod G f (gs - {h}) \<in> generate G gs"
          from fgsh have fgsgs: "finprod G f (gs - {h}) \<in> generate G gs" using mono_generate[of "gs - {h}" gs] by blast
          have fPi: "f \<in> (\<Pi> a\<in>(gs - {h}). generate G {a})" using f by blast
          have gI: "generate G (gs - {h}) = (\<lambda>x. finprod G x (gs - {h})) ` (\<Pi> a\<in>gs - {h}. generate G {a})"
            using generate_eq_finprod_Pi_image[of "gs - {h}"] assms(1, 2) by blast
          have fgno: "f g \<noteq> \<one>"
          proof (rule ccontr)
            assume o: "\<not> f g \<noteq> \<one>"
            hence kf: "k = finprod G f (gs - {h})" using kp finprod_closed fc by auto
            hence "k \<in> generate G (gs - {h})" using fPi gI by blast
            thus False using k ca h unfolding complementary_def by blast
          qed
          from fpgs have "f g \<in> generate G gs"
            using subgroup.mult_in_cancel_right[OF generate_is_subgroup[OF assms(2)] fc[of g] fgsgs]
            by blast
          with fgno assms(5) fg[of g] show "False" unfolding complementary_def by blast
        qed
        moreover have "k \<in> generate G gs" using k(1) mono_generate[of "{h}" gs] h(1) by blast
        ultimately show False using kp by blast
      qed
    qed
  qed simp
qed


lemma (in comm_group) stronger_PiE_finprod_imp:
  assumes "A \<subseteq> carrier G" "\<forall>f \<in> Pi\<^sub>E A (\<lambda>a. generate G {a}). finprod G f A = \<one> \<longrightarrow> (\<forall>a\<in>A. f a = \<one>)"
  shows "\<forall>f \<in> Pi\<^sub>E ((\<lambda>a. generate G {a}) ` A) id. finprod G f ((\<lambda>a. generate G {a}) ` A) = \<one> \<longrightarrow> (\<forall>H\<in> (\<lambda>a. generate G {a}) ` A. f H = \<one>)"
proof(rule, rule)
  fix f
  assume f: "f \<in> Pi\<^sub>E ((\<lambda>a. generate G {a}) ` A) id" "finprod G f ((\<lambda>a. generate G {a}) ` A) = \<one>"
  define B where "B = inv_into A (\<lambda>a. generate G {a}) ` ((\<lambda>a. generate G {a}) ` A)"
  have Bs: "B \<subseteq> A"
  proof
    fix x
    assume x: "x \<in> B"
    then obtain C where C: "C \<in> ((\<lambda>a. generate G {a}) ` A)" "x = inv_into A (\<lambda>a. generate G {a}) C" unfolding B_def by blast
    then obtain c where c: "C = generate G {c}" "c \<in> A" by blast
    with C someI_ex[of "\<lambda>y. y \<in> A \<and> generate G {y} = C"] show "x \<in> A" unfolding inv_into_def by blast
  qed
  have sI: "(\<lambda>x. generate G {x}) ` B = (\<lambda>x. generate G {x}) ` A"
  proof
    show "(\<lambda>x. generate G {x}) ` B \<subseteq> (\<lambda>x. generate G {x}) ` A" using Bs by blast
    show "(\<lambda>x. generate G {x}) ` A \<subseteq> (\<lambda>x. generate G {x}) ` B"
    proof
      fix C
      assume C: "C \<in> (\<lambda>x. generate G {x}) ` A"
      then obtain x where x: "x = inv_into A (\<lambda>a. generate G {a}) C" unfolding B_def by blast
      then obtain c where c: "C = generate G {c}" "c \<in> A" using C by blast
      with C x someI_ex[of "\<lambda>y. y \<in> A \<and> generate G {y} = C"] have "generate G {x} = C" unfolding inv_into_def by blast
      with x C show "C \<in> (\<lambda>x. generate G {x}) ` B" unfolding B_def by blast
    qed
  qed
  have fBc: "f (generate G {b}) \<in> carrier G" if "b \<in> B" for b
  proof -
    have "f (generate G {b}) \<in> generate G {b}" using f(1) by(subst (asm) sI[symmetric], use that in fastforce)
    moreover have "generate G {b} \<subseteq> carrier G" using assms(1) that Bs generate_incl by blast
    ultimately show ?thesis by blast
  qed
  let ?r = "restrict (\<lambda>a. if a\<in>B then f (generate G {a}) else \<one>) A"
  have "?r \<in> Pi\<^sub>E A (\<lambda>a. generate G {a})"
  proof
    show "?r x = undefined" if "x \<notin> A" for x using that by simp
    show "?r x \<in> generate G {x}" if "x \<in> A" for x using that generate.one B_def f(1) by auto
  qed
  moreover have "finprod G ?r A = \<one>"
  proof (cases "finite A")
    case True
    have "A = B \<union> (A - B)" using Bs by auto
    then have "finprod G ?r A = finprod G ?r (B\<union>(A-B))" by auto
    moreover have "\<dots> = finprod G ?r B \<otimes> finprod G ?r (A - B)"
    proof(intro finprod_Un_disjoint)
      from True Bs finite_subset show "finite B" "finite (A - B)" "B \<inter> (A - B) = {}" by auto
      show "(\<lambda>a\<in>A. if a \<in> B then f (generate G {a}) else \<one>) \<in> A - B \<rightarrow> carrier G" using Bs by simp
      from fBc show "(\<lambda>a\<in>A. if a \<in> B then f (generate G {a}) else \<one>) \<in> B \<rightarrow> carrier G" using Bs by auto
    qed
    moreover have "finprod G ?r B = \<one>"
    proof -
      have "finprod G ?r B = finprod G (f \<circ> (\<lambda>a. generate G {a})) B"
      proof(intro finprod_cong')
        show "?r b = (f \<circ> (\<lambda>a. generate G {a})) b" if "b \<in> B" for b using that Bs by auto
        show "f \<circ> (\<lambda>a. generate G {a}) \<in> B \<rightarrow> carrier G" using fBc by simp
      qed simp
      also have "\<dots> = finprod G f ((\<lambda>a. generate G {a}) ` B)"
      proof(intro finprod_comp[symmetric])
        show "(f \<circ> (\<lambda>a. generate G {a})) ` B \<subseteq> carrier G" using fBc by auto
        show "inj_on (\<lambda>a. generate G {a}) B" by(intro inj_onI, unfold B_def, metis (no_types, lifting) f_inv_into_f inv_into_into)
      qed
      also have "\<dots> = finprod G f ((\<lambda>a. generate G {a}) ` A)" using sI by argo
      finally show ?thesis using f(2) by argo
    qed
    moreover have "finprod G ?r (A - B) = \<one>" by(intro finprod_one_eqI, simp)
    ultimately show ?thesis by fastforce
  next
    case False
    then show ?thesis unfolding finprod_def by simp
  qed
  ultimately have a: "\<forall>a\<in>A. ?r a = \<one>" using assms(2) by blast
  then have BA: "\<forall>a\<in>B\<inter>A. ?r a = \<one>" by blast
  from Bs sI have "\<forall>a\<in>A. (generate G {a}) \<in> ((\<lambda>x. generate G {x}) ` B)" by simp
  then have "\<forall>a\<in>A. \<exists>b\<in>B. f (generate G {a}) = f (generate G {b})" by force
  thus "\<forall>H\<in>(\<lambda>a. generate G {a}) ` A. f H = \<one>" using a BA Bs by fastforce
qed


(* Manuel *)
lemma Sigma_insert: "Sigma (insert x A) B = (\<lambda>y. (x, y)) ` B x \<union> Sigma A B"
  by auto

(* Manuel, TODO: move to library *)
lemma (in comm_monoid) finprod_Sigma:
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> g x y \<in> carrier G"
  shows   "(\<Otimes>x\<in>A. \<Otimes>y\<in>B x. g x y) = (\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y)"
  using assms
proof (induction A rule: finite_induct)
  case (insert x A)
  have "(\<Otimes>z\<in>Sigma (insert x A) B. case z of (x, y) \<Rightarrow> g x y) =
          (\<Otimes>z\<in>Pair x ` B x. case z of (x, y) \<Rightarrow> g x y) \<otimes> (\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y)"
    unfolding Sigma_insert using insert.prems insert.hyps
    by (subst finprod_Un_disjoint) auto
  also have "(\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y) = (\<Otimes>x\<in>A. \<Otimes>y\<in>B x. g x y)"
    using insert.prems insert.hyps by (subst insert.IH [symmetric]) auto
  also have "(\<Otimes>z\<in>Pair x ` B x. case z of (x, y) \<Rightarrow> g x y) = (\<Otimes>y\<in>B x. g x y)"
    using insert.prems insert.hyps by (subst finprod_reindex) (auto intro: inj_onI)
  finally show ?case
    using insert.hyps insert.prems by simp
qed auto

end