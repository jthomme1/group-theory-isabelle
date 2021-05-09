theory Finite_Cyclic
  imports IDirProds Group_Hom
begin

locale finite_group = group +
  assumes fin[simp]: "finite (carrier G)"

locale finite_comm_group = finite_group + comm_group

locale cyclic_group = group +
  fixes gen :: "'a"
  assumes gen_closed[intro, simp]: "gen \<in> carrier G"
  assumes generator: "carrier G = generate G {gen}"

locale finite_cyclic_group = finite_group + cyclic_group

lemma (in cyclic_group) elem_is_gen_pow:
  assumes "x \<in> carrier G"
  shows "\<exists>n :: int. x = gen [^] n"
proof -
  from generator have x_g:"x \<in> generate G {gen}" using assms by fast
  with generate_pow[of gen] show ?thesis using gen_closed by blast
qed

sublocale cyclic_group \<subseteq> comm_group
proof(unfold_locales)
  fix x y
  assume "x \<in> carrier G" "y \<in> carrier G"
  then obtain a b where ab:"x = gen [^] (a::int)" "y = gen [^] (b::int)" using elem_is_gen_pow by presburger
  then have "x \<otimes> y = gen [^] (a + b)" by (simp add: int_pow_mult)                 
  also have "\<dots> = y \<otimes> x" using ab int_pow_mult
    by (metis add.commute gen_closed)
  finally show "x \<otimes> y = y \<otimes> x" .
qed

sublocale finite_cyclic_group \<subseteq> finite_comm_group
  by unfold_locales

lemma (in group) cyclic_groupI0:
  assumes "a \<in> carrier G" "carrier G = generate G {a}"
  shows "cyclic_group G a"
  using assms by (unfold_locales; auto) 

lemma (in group) cyclic_groupI1:
  assumes "a \<in> carrier G" "carrier G \<subseteq> generate G {a}"
  shows "cyclic_group G a"
  using assms by (unfold_locales, use generate_incl[of "{a}"] in auto)

lemma (in group) cyclic_groupI2:
  assumes "a \<in> carrier G"
  shows "cyclic_group (G\<lparr>carrier := generate G {a}\<rparr>) a"
proof (intro group.cyclic_groupI0)
  show "group (G\<lparr>carrier := generate G {a}\<rparr>)" by(intro subgroup.subgroup_is_group group.generate_is_subgroup, use assms in simp_all)
  show "a \<in> carrier (G\<lparr>carrier := generate G {a}\<rparr>)" using generate.incl[of a "{a}"] by auto
  show "carrier (G\<lparr>carrier := generate G {a}\<rparr>) = generate (G\<lparr>carrier := generate G {a}\<rparr>) {a}"
    using assms
    by (simp add: generate_consistent generate.incl group.generate_is_subgroup)
qed

lemma (in finite_group) finite_generate:
  assumes "A \<subseteq> carrier G"
  shows "finite (generate G A)"
  using generate_incl[of A] rev_finite_subset[of "carrier G" "generate G A"] assms by simp

lemma (in finite_group) generate_induct[consumes 1, case_names base adjoin]:
  assumes "A0 \<subseteq> carrier G"
  assumes "A0 \<subseteq> carrier G \<Longrightarrow> P (G\<lparr>carrier := generate G A0\<rparr>)"
  assumes "\<And>a A. \<lbrakk>A \<subseteq> carrier G; a \<in> carrier G - generate G A; A0 \<subseteq> A; P (G\<lparr>carrier := generate G A\<rparr>)\<rbrakk> \<Longrightarrow> P (G\<lparr>carrier := generate G (A \<union> {a})\<rparr>)"
  shows "P G"
proof -
  define A where A: "A = carrier G"
  hence gA: "generate G A = carrier G" using generate_incl[of "carrier G"] generate_sincl[of "carrier G"] by simp
  hence "finite A" using fin A by argo
  moreover have "A0 \<subseteq> A" using assms(1) A by argo
  moreover have "A \<subseteq> carrier G" using A by simp
  moreover have "generate G A0 \<subseteq> generate G A" using gA generate_incl[OF assms(1)] by argo
  ultimately have "P (G\<lparr>carrier := generate G A\<rparr>)" using assms(2, 3)
  proof (induction "A" taking: card rule: measure_induct_rule)
    case (less A)
    then show ?case
    proof(cases "generate G A0 = generate G A")
      case True
      thus ?thesis using less by force
    next
      case gA0: False
      with less(3) have s: "A0 \<subset> A" by blast
      then obtain a where a: "a \<in> A - A0" by blast
      have P1: "P (G\<lparr>carrier := generate G (A - {a})\<rparr>)"
      proof(rule less(1))
        show "card (A - {a}) < card A" using a less(2) by (meson DiffD1 card_Diff1_less)
        show "A0 \<subseteq> A - {a}" using a s by blast
        thus "generate G A0 \<subseteq> generate G (A - {a})" using mono_generate by presburger
      qed (use less a s in auto)
      show ?thesis
      proof (cases "generate G A = generate G (A - {a})")
        case True
        then show ?thesis using P1 by simp
      next
        case False
        have "a \<in> carrier G - generate G (A - {a})"
        proof -
          have "a \<notin> generate G (A - {a})"
          proof
            assume a2: "a \<in> generate G (A - {a})"
            have "generate G (A - {a}) = generate G A"
            proof (rule equalityI)
              show "generate G (A - {a}) \<subseteq> generate G A" using mono_generate by auto
              show "generate G A \<subseteq> generate G (A - {a})"
              proof(subst (2) generate_idem[symmetric])
                show "generate G A \<subseteq> generate G (generate G (A - {a}))" by (intro mono_generate, use generate_sincl[of "A - {a}"] a2 in blast)
              qed (use less in auto)
            qed
            with False show False by argo
          qed
          with a less show ?thesis by fast
        qed
        from less(7)[OF _ this _ P1] less(4) s a have "P (G\<lparr>carrier := generate G (A - {a} \<union> {a})\<rparr>)" by blast
        moreover have "A - {a} \<union> {a} = A" using a by blast
        ultimately show ?thesis by auto
      qed
    qed
  qed
  with gA show ?thesis by simp
qed


lemma (in finite_group) all_prime_factors_multiplicity_sylow_groups:
  "\<forall>p \<in> prime_factors (order G). \<exists>H. subgroup H G \<and> card H = p ^ multiplicity p (order G)"
proof
  fix p
  assume pf: "p \<in># prime_factorization (order G)"
  show "\<exists>H. subgroup H G \<and> card H = p ^ multiplicity p (order G)"
  proof -
    from pf have "Factorial_Ring.prime p" using in_prime_factors_iff[of p "order G"] by blast
    have "p ^ multiplicity p (order G) dvd order G" using multiplicity_dvd[of p "order G"] . 
    then obtain m where "order G = p ^ multiplicity p (order G) * m" by blast
    then show ?thesis using sylow_thm[of p G "multiplicity p (order G)" m] \<open>Factorial_Ring.prime p\<close> by fastforce 
  qed
qed

lemma (in finite_group) prime_factor_multiplicity_sylow_groups:
  assumes "p \<in> prime_factors (order G)"
  shows "\<exists>H. subgroup H G \<and> card H = p ^ multiplicity p (order G)"
  using all_prime_factors_multiplicity_sylow_groups assms
    Set.bspec[of "prime_factors (order G)" "\<lambda>p. \<exists>H. subgroup H G \<and> card H = p ^ multiplicity p (order G)" p]
    by blast

lemma (in finite_group) prime_factor_subgroup:
  assumes "p \<in> prime_factors (order G)"
  shows "\<exists>H. subgroup H G \<and> card H = p"
proof -
  from assms have "p dvd (order G)" by blast
  then obtain l where "l * p = order G" by fastforce
  then show ?thesis using assms sylow_thm[of p G 1 l] fin by force
qed

lemma (in finite_group) card_sum:
  assumes "subgroup P G" "subgroup Q G"
  shows "card (IDirProd G P Q) \<ge> lcm (card P) (card Q)"
proof -
  from sub_sub_generate_dvd_order[of P Q] have "card P dvd card (generate G (P \<union> Q))" using assms by blast
  moreover from sub_sub_generate_dvd_order[of Q P] have "card Q dvd card (generate G (P \<union> Q))" using assms Un_commute by metis
  moreover have "\<one> \<in> (generate G (P \<union> Q))" using generate.one[of G "P \<union> Q"] by presburger
  moreover from this have "card (generate G (P \<union> Q)) \<noteq> 0" using card_eq_0_iff[of "generate G (P \<union> Q)"] finite_generate[of "P \<union> Q"] assms
    by (metis IDirProd_def IDirProd_is_subgroup equals0D fin finite_subset subgroup.subset)
  ultimately show ?thesis using lcm_is_Min_multiple_nat[of "card (generate G (P \<union> Q))" "card P" "card Q"] IDirProd_def[of G P Q] by presburger
qed

lemma (in finite_group) prime_factor_multiplicity_card_sum:
  assumes "subgroup P G" "subgroup Q G" "coprime (card P) (card Q)"
  shows "card (IDirProd G P Q) \<ge> card P * card Q"
  using coprime_iff_gcd_eq_1[of "card P" "card Q"] prod_gcd_lcm_nat[of "card P" "card Q"] card_sum[of P Q] assms by fastforce

lemma (in finite_group) bigger_subgroup_is_group:
  assumes "subgroup H G" "card H \<ge> order G"
  shows "H = carrier G"
  using subgroup.subset[of H G] order_def[of G] assms card_mono[of "carrier G" H] fin card_subset_eq[of "carrier G" H] by linarith

lemma (in finite_group) element_ord_generates_cyclic:
  assumes "a \<in> carrier G" "ord a = order G"
  shows "cyclic_group G a"
proof (unfold_locales)
  show "a \<in> carrier G" using assms(1) by simp
  have "carrier G = generate G {a}"
    using generate_pow_card[of a] card_subset_eq[of "carrier G" "generate G {a}"] generate_incl[of "{a}"] order_def[of G] assms finite_group_axioms finite_group_axioms_def[of G]
    by fastforce
  thus "carrier G = generate G {a}" by auto
qed

lemma (in group) prime_order_group_is_cyc:
  assumes "\<exists>p. order G = p \<and> Factorial_Ring.prime p"
  obtains g where "cyclic_group G g"
proof (unfold_locales)
  obtain p where order_p: "order G = p" and p_prime: "Factorial_Ring.prime p" using assms by blast
  then have "card (carrier G) \<ge> 2" by (simp add: order_def prime_ge_2_nat)
  then obtain a where a_in: "a \<in> carrier G" and a_not_one: "a \<noteq> \<one>" using one_unique
    by (metis (no_types, lifting) card_2_iff' obtain_subset_with_card_n subset_iff)
  interpret fin: finite_group G
    using assms order_gt_0_iff_finite unfolding order_def by unfold_locales auto
  have "ord a dvd p" using a_in order_p ord_dvd_group_order by blast
  hence "ord a = p" using prime_nat_iff[of p] p_prime ord_eq_1 a_in a_not_one by blast
  then interpret cyclic_group G a
    using fin.element_ord_generates_cyclic order_p a_in by simp
  show ?thesis using that cyclic_group_axioms .
qed

lemma (in finite_cyclic_group) ord_gen_gt_zero:
  "ord gen > 0"
  using ord_ge_1[OF fin gen_closed] by simp

lemma (in finite_cyclic_group) generate_nat_pow:
  "generate G {gen} = {gen [^] k |k. k \<in> {0..ord gen - 1}}"
  using ord_gen_gt_zero generate_nat_pow[OF _ gen_closed] by simp

lemma (in finite_cyclic_group) generate_nat_pow':
  "generate G {gen} = {gen [^] k |k. k \<in> {0..<ord gen}}"
  using generate_nat_pow ord_gen_gt_zero by force

lemma (in finite_cyclic_group) ord_gen_non_zero_card_gen:
  "ord gen = card(generate G {gen})"
proof -
  define n where n: "n = ord gen"
  hence np: "n > 0" using ord_gen_gt_zero by simp
  have "card {0..n - 1} = n" by (simp add: np)
  then have cn:"card (([^]) gen ` {0..n - 1}) = n"
    using card_image[of "([^]) gen" "{0..n - 1}"] ord_inj[of gen]
      gen_closed image_def[of "([^]) gen" "{0..n - 1}"] n by argo
  have "([^]) gen ` {0..n - 1} = {gen [^] k|k::nat. k \<in> {0..n - 1}}" by blast
  then have "card {gen [^] k|k::nat. k \<in> {0..n - 1}} = n"
    using image_def[of "([^]) gen" "{0..n - 1}"] cn by argo
  with generate_nat_pow show ?thesis using n by algebra
qed

lemma (in cyclic_group) infinite_imp_ord_gen_0:
  assumes "infinite (carrier G)"
  shows "ord gen = 0"
  using assms generate_pow_card generator by fastforce

lemma (in cyclic_group) ord_gen_is_group_order:
  shows "ord gen = order G"
proof (cases "finite (carrier G)")
  case True
  then interpret finite_cyclic_group G gen by unfold_locales
  from generator show "ord gen = order G"
    using generate_pow_card[of gen] order_def[of G] gen_closed fin by argo
next
  case False
  thus ?thesis
    using infinite_imp_ord_gen_0 order_def[of G] card_eq_0_iff[of "carrier G"] by presburger
qed

(* Manuel *)
lemma (in finite_group) ord_pos: 
  assumes "x \<in> carrier G"
  shows   "ord x > 0"
  using ord_ge_1[of x] assms by auto

lemma (in finite_group) order_gt_0 [simp,intro]: "order G > 0"
  by (subst order_gt_0_iff_finite) auto

lemma (in finite_comm_group) subgroup_imp_finite_comm_group:
  assumes "subgroup H G"
  shows   "finite_comm_group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret G': group "G\<lparr>carrier := H\<rparr>" by (intro subgroup_imp_group) fact+
  interpret H: subgroup H G by fact
  show ?thesis by standard (use finite_subset[OF H.subset] in \<open>auto simp: m_comm\<close>)
qed

(* Manuel *)
lemma (in cyclic_group) generator_induct [consumes 1, case_names generate inv]:
  assumes x: "x \<in> carrier G"
  assumes IH1: "\<And>n::nat. P (gen [^] n)"
  assumes IH2: "\<And>x. x \<in> carrier G \<Longrightarrow> P x \<Longrightarrow> P (inv x)"
  shows   "P x"
proof -
  from x obtain n :: int where n: "x = gen [^] n"
    using elem_is_gen_pow[of x] by auto
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    have "P (gen [^] nat n)"
      by (rule IH1)
    with True n show ?thesis by simp
  next
    case False
    have "P (inv (gen [^] nat (-n)))"
      by (intro IH1 IH2) auto
    also have "gen [^] nat (-n) = gen [^] (-n)"
      using False by simp
    also have "inv \<dots> = x"
      using n by (simp add: int_pow_neg)
    finally show ?thesis .
  qed
qed

lemma (in finite_cyclic_group) generator_induct0 [consumes 1, case_names one step]:
  assumes x: "x \<in> carrier G"
  assumes IH1: "P \<one>"
  assumes IH2: "\<And>x. \<lbrakk>x \<in> carrier G; P x\<rbrakk> \<Longrightarrow> P (x \<otimes> gen)"
  shows   "P x"
proof -
  from generate_nat_pow obtain n::nat where n: "x = gen [^] n" using generator x by blast
  thus ?thesis by (induction n arbitrary: x, use assms in auto)
qed

lemma (in finite_cyclic_group) generator_induct1 [consumes 1, case_names gen step]:
  assumes x: "x \<in> carrier G"
  assumes IH1: "P gen"
  assumes IH2: "\<And>x. \<lbrakk>x \<in> carrier G; P x\<rbrakk> \<Longrightarrow> P (x \<otimes> gen)"
  shows   "P x"
proof(rule generator_induct0[OF x])
  show "\<And>x. \<lbrakk>x \<in> carrier G; P x\<rbrakk> \<Longrightarrow> P (x \<otimes> gen)" using IH2 by blast
  have "P x" if "n > 0" "x = gen [^] n" for n::nat and x using that
    by (induction n arbitrary: x; use assms in fastforce)
  from this[OF ord_pos[OF gen_closed] pow_ord_eq_1[OF gen_closed, symmetric]] show "P \<one>" .
qed

lemma (in finite_group) finite_ord_conv_Least:
  assumes "x \<in> carrier G"
  shows "ord x = (LEAST n::nat. 0 < n \<and> x [^] n = \<one>)"
  using pow_order_eq_1 order_gt_0_iff_finite ord_conv_Least assms by auto

lemma (in finite_group) non_trivial_group_ord_gr_1:
  assumes "carrier G \<noteq> {\<one>}"
  shows "\<exists>e \<in> carrier G. ord e > 1"
proof -
  from one_closed obtain e where e:"e \<noteq> \<one>" "e \<in> carrier G" using assms carrier_not_empty by blast
  thus ?thesis using ord_eq_1[of e] le_neq_implies_less ord_ge_1 by fastforce
qed

lemma (in finite_group) max_order_elem: (* Manuel *)
  obtains a where "a \<in> carrier G" "\<forall>x \<in> carrier G. ord x \<le> ord a"
proof -
  have "\<exists>x. x \<in> carrier G \<and> (\<forall>y. y \<in> carrier G \<longrightarrow> ord y \<le> ord x)"
  proof (rule ex_has_greatest_nat[of _ \<one> _ "order G + 1"], safe)
    show "\<one> \<in> carrier G"
      by auto
  next
    fix x assume "x \<in> carrier G"
    hence "ord x \<le> order G"
      by (intro ord_le_group_order fin)
    also have "\<dots> < order G + 1"
      by simp
    finally show "ord x < order G + 1" .
  qed
  thus ?thesis using that by blast
qed

lemma (in cyclic_group) Pi_generate_cong:
  assumes "\<And>H. H \<in> Hs \<Longrightarrow> (generate G {f H} = H)" 
  shows "Pi Hs id = Pi Hs (\<lambda>x. generate G {f x})"
  unfolding Pi_def using assms by simp

lemma (in cyclic_group) Pi_generate_int_cong:
  assumes "f \<in> Hs \<rightarrow> carrier G" "\<And>H. H \<in> Hs \<Longrightarrow> (generate G {f H} = H)" 
  shows "Pi Hs id = Pi Hs (\<lambda>x. { (f x) [^] (k :: int) | k. k \<in> UNIV })"
  using assms Pi_generate_cong[OF assms(2), of Hs] generate_pow by blast    

lemma (in group) iso_cyclic_groups_generate:
  assumes "a \<in> carrier G" "b \<in> carrier H" "group.ord G a = group.ord H b" "group H"
  shows "{f. \<forall>k \<in> (UNIV::int set). f (a [^] k) = b [^]\<^bsub>H\<^esub> k} \<subseteq> iso (G\<lparr>carrier := generate G {a}\<rparr>) (H\<lparr>carrier := generate H {b}\<rparr>)"
proof
  interpret H: group H by fact
  let ?A = "G\<lparr>carrier := generate G {a}\<rparr>"
  let ?B = "H\<lparr>carrier := generate H {b}\<rparr>"
  interpret A: cyclic_group ?A a by(intro group.cyclic_groupI2; use assms(1) in simp)
  interpret B: cyclic_group ?B b by(intro group.cyclic_groupI2; use assms(2) in simp)
  have sA: "subgroup (generate G {a}) G" by(intro generate_is_subgroup, use assms(1) in simp)
  have sB: "subgroup (generate H {b}) H" by(intro H.generate_is_subgroup, use assms(2) in simp)
  fix x
  assume x: "x \<in> {f. \<forall>k\<in>(UNIV::int set). f (a [^] k) = b [^]\<^bsub>H\<^esub> k}"
  have hom: "x \<in> hom ?A ?B"
  proof (intro homI)
    fix c
    assume c: "c \<in> carrier ?A"
    from A.elem_is_gen_pow[OF this] obtain k::int where k: "c = a [^] k" using int_pow_consistent[OF sA generate.incl[of a]] by auto
    with x have "x c = b [^]\<^bsub>H\<^esub> k" by blast
    thus "x c \<in> carrier ?B"
      using B.int_pow_closed H.int_pow_consistent[OF sB] generate.incl[of b "{b}" H] by simp
    fix d
    assume d: "d \<in> carrier ?A"
    from A.elem_is_gen_pow[OF this] obtain l::int where l: "d = a [^] l" using int_pow_consistent[OF sA generate.incl[of a]] by auto
    with k have "c \<otimes> d = a [^] (k + l)" by (simp add: int_pow_mult assms(1))
    with x have "x (c \<otimes>\<^bsub>?A\<^esub> d) = b [^]\<^bsub>H\<^esub> (k + l)" by simp
    also have "\<dots> = b [^]\<^bsub>H\<^esub> k \<otimes>\<^bsub>H\<^esub> b [^]\<^bsub>H\<^esub> l" by (simp add: H.int_pow_mult assms(2))
    finally show "x (c \<otimes>\<^bsub>?A\<^esub> d) = x c \<otimes>\<^bsub>?B\<^esub> x d" using x k l by simp
  qed
  then interpret xgh: group_hom ?A ?B x unfolding group_hom_def group_hom_axioms_def by blast
  have "kernel ?A ?B x = {\<one>}"
  proof(intro equalityI)
    show "{\<one>} \<subseteq> kernel ?A ?B x" using xgh.one_in_kernel by auto
    have "c = \<one>" if "c \<in> kernel ?A ?B x" for c
    proof -
      from that have c: "c \<in> carrier ?A" unfolding kernel_def by blast
      from A.elem_is_gen_pow[OF this] obtain k::int where k: "c = a [^] k" using int_pow_consistent[OF sA generate.incl[of a]] by auto
      moreover have "x c = \<one>\<^bsub>H\<^esub>" using that x unfolding kernel_def by auto
      ultimately have "\<one>\<^bsub>H\<^esub> = b [^]\<^bsub>H\<^esub> k" using x by simp
      with assms(3) have "a [^] k = \<one>" using int_pow_eq_id[OF assms(1), of k] H.int_pow_eq_id[OF assms(2), of k] by simp
      thus "c = \<one>" using k by blast
    qed
    thus "kernel ?A ?B x \<subseteq> {\<one>}" by blast             
  qed
  moreover have "carrier ?B \<subseteq> x ` carrier ?A"
  proof
    fix c
    assume c: "c \<in> carrier ?B"
    from B.elem_is_gen_pow[OF this] obtain k::int where k: "c = b [^]\<^bsub>H\<^esub> k" using H.int_pow_consistent[OF sB generate.incl[of b]] by auto
    then have "x (a [^] k) = c" using x by blast
    moreover have "a [^] k \<in> carrier ?A"
      using int_pow_consistent[OF sA generate.incl[of a]] A.int_pow_closed generate.incl[of a] by fastforce
    ultimately show "c \<in> x ` carrier ?A" by blast
  qed
  ultimately show "x \<in> iso ?A ?B" using hom xgh.iso_iff unfolding kernel_def by auto
qed

definition (in group) get_exp where
  "get_exp g = (\<lambda>a. SOME k::int. a = g [^] k)"

lemma (in cyclic_group) get_exp_fulfills:
  assumes "a \<in> carrier G"
  shows "a = gen [^] get_exp gen a"
proof -
  from elem_is_gen_pow[OF assms] obtain k::int where k: "a = gen [^] k" by blast
  moreover have "gen [^] k = gen [^] (SOME x::int. gen [^] k = gen [^] x)"
    by(intro someI_ex[of "\<lambda>x::int. gen [^] k = gen [^] x"]; blast)
  ultimately show ?thesis unfolding get_exp_def by blast
qed

lemma (in cyclic_group) get_exp_non_zero:
  assumes"b \<in> carrier G" "b \<noteq> \<one>"
  shows "get_exp gen b \<noteq> 0"
  using assms get_exp_fulfills[OF assms(1)] by auto 

lemma (in cyclic_group) get_exp_mult_mod:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "get_exp gen (a \<otimes> b) mod (ord gen) = (get_exp gen a + get_exp gen b) mod (ord gen)"
proof (intro pow_eq_int_mod[OF gen_closed])
  from get_exp_fulfills[of "a \<otimes> b"] have "gen [^] get_exp gen (a \<otimes> b) = a \<otimes> b" using assms by simp
  moreover have "gen [^] (get_exp gen a + get_exp gen b) = a \<otimes> b"
  proof -
    have "gen [^] (get_exp gen a + get_exp gen b) = gen [^] (get_exp gen a) \<otimes> gen [^] (get_exp gen b)"
      using int_pow_mult by blast
    with get_exp_fulfills assms show ?thesis by simp
  qed
  ultimately show "gen [^] get_exp gen (a \<otimes> b) = gen [^] (get_exp gen a + get_exp gen b)" by simp
qed

lemma (in group) get_exp_self_fulfills:
  assumes "a \<in> carrier G"
  shows "a = a [^] get_exp a a"
proof -
  have "a = a [^] (1::int)" using assms by auto
  moreover have "a [^] (1::int) = a [^] (SOME x::int. a [^] (1::int) = a [^] x)"
    by (intro someI_ex[of "\<lambda>x::int. a [^] (1::int) = a [^] x"]; blast)
  ultimately show ?thesis unfolding get_exp_def by simp
qed

lemma (in group) get_exp_self:
  assumes "a \<in> carrier G" shows "get_exp a a mod ord a = (1::int) mod ord a"
  by (intro pow_eq_int_mod[OF assms], use get_exp_self_fulfills[OF assms] assms in auto)

lemma (in group) powi_get_exp_self:
  fixes z::complex
  assumes "z ^ n = 1" "x \<in> carrier G" "ord x = n" "n > 1"
  shows "z powi get_exp x x = z"
proof -
  from assms have ngt0: "n > 0" by simp
  from powi_mod[OF assms(1) ngt0, of "get_exp x x"] get_exp_self[OF assms(2), unfolded assms(3)]
  have "z powi get_exp x x = z powi (1 mod int n)" by argo
  also have "\<dots> = z" using assms(4) by simp
  finally show ?thesis .
qed

lemma (in cyclic_group) iso_cyclic_groups_same_order:
  assumes "cyclic_group H h" "order G = order H"
  shows "G \<cong> H"
proof(intro is_isoI)
  interpret H: cyclic_group H h by fact
  define f where "f = (\<lambda>a. h [^]\<^bsub>H\<^esub> get_exp gen a)"
  from assms(2) have o: "ord gen = H.ord h" using ord_gen_is_group_order H.ord_gen_is_group_order by simp
  have "\<forall>k \<in> (UNIV::int set). f (gen [^] k) = h [^]\<^bsub>H\<^esub> k"
  proof
    fix k
    assume k: "k \<in> (UNIV::int set)"
    have "gen [^] k = gen [^] (SOME x::int. gen [^] k = gen [^] x)"
      by(intro someI_ex[of "\<lambda>x::int. gen [^] k = gen [^] x"]; blast)
    moreover have "(SOME x::int. gen [^] k = gen [^] x) = (SOME x::int. h [^]\<^bsub>H\<^esub> k = h [^]\<^bsub>H\<^esub> x)"
    proof -
      have "gen [^] k = gen [^] x \<longleftrightarrow> h [^]\<^bsub>H\<^esub> k = h [^]\<^bsub>H\<^esub> x" for x::int
        by (simp add: o group.int_pow_eq)  
      thus ?thesis by simp
    qed
    moreover have "h [^]\<^bsub>H\<^esub> k = h [^]\<^bsub>H\<^esub> (SOME x::int. h [^]\<^bsub>H\<^esub> k = h [^]\<^bsub>H\<^esub> x)"
      by(intro someI_ex[of "\<lambda>x::int. h [^]\<^bsub>H\<^esub> k = h [^]\<^bsub>H\<^esub> x"]; blast)
    ultimately show "f (gen [^] k) = h [^]\<^bsub>H\<^esub> k" unfolding f_def get_exp_def by metis
  qed
  thus "f \<in> iso G H"
    using iso_cyclic_groups_generate[OF gen_closed H.gen_closed o H.is_group]
    by (auto simp flip: generator H.generator)
qed

lemma (in finite_group) iso_imp_finite:
  assumes "G \<cong> H" "group H"
  shows "finite_group H"
proof -
  interpret H: group H by fact
  show ?thesis
  proof(unfold_locales)
    show "finite (carrier H)" using iso_same_card[OF assms(1)]
      by (metis card_gt_0_iff order_def order_gt_0)
  qed
qed

lemma (in finite_comm_group) iso_imp_finite_comm:
  assumes "G \<cong> H" "group H"
  shows "finite_comm_group H"
proof -
  interpret H: group H by fact
  interpret H: comm_group H by (intro iso_imp_comm_group[OF assms(1)], unfold_locales)
  interpret H: finite_group H by (intro iso_imp_finite[OF assms(1)], unfold_locales)
  show ?thesis by unfold_locales
qed

lemma (in finite_group) finite_FactGroup:
  assumes "H \<lhd> G"
  shows "finite_group (G Mod H)"
proof -
  interpret H: normal H G by fact
  interpret Mod: group "G Mod H" using H.factorgroup_is_group .
  show ?thesis
    by (unfold_locales, unfold FactGroup_def RCOSETS_def, simp)
qed

lemma (in finite_comm_group) finite_comm_FactGroup:
  assumes "subgroup H G"
  shows "finite_comm_group (G Mod H)"
  unfolding finite_comm_group_def
proof(safe)
  show "finite_group (G Mod H)" using finite_FactGroup[OF subgroup_imp_normal[OF assms]] .
  show "comm_group (G Mod H)" by (simp add: abelian_FactGroup assms)
qed

abbreviation Z where "Z \<equiv> integer_mod_group"

lemma Zn_neq1_cyclic_group:
  assumes "n \<noteq> 1"
  shows "cyclic_group (Z n) 1"
proof(unfold cyclic_group_def cyclic_group_axioms_def, safe)
  show "group (Z n)" using group_integer_mod_group .
  then interpret group "Z n" .
  show oc: "1 \<in> carrier (Z n)" unfolding integer_mod_group_def integer_group_def using assms by force
  show "x \<in> generate (Z n) {1}" if "x \<in> carrier (Z n)" for x
    using generate_pow[OF oc] that int_pow_integer_mod_group solve_equation subgroup_self by fastforce
  show "x \<in> carrier (Z n)" if "x \<in> generate (Z n) {1}" for x using generate_incl[of "{1}"] that oc by fast
qed

lemma Z1_cyclic_group: "cyclic_group (Z 1) 0"
proof(unfold cyclic_group_def cyclic_group_axioms_def, safe)
  show "group (Z 1)" using group_integer_mod_group .
  then interpret group "Z 1" .
  show "0 \<in> carrier (Z 1)" unfolding integer_mod_group_def by simp
  thus "x \<in> carrier (Z 1)" if "x \<in> generate (Z 1) {0}" for x using generate_incl[of "{0}"] that by fast
  show "x \<in> generate (Z 1) {0}" if "x \<in> carrier (Z 1)" for x
  proof -
    from that have "x = 0" unfolding integer_mod_group_def by auto
    with generate.one[of "Z 1" "{0}"] show "x \<in> generate (Z 1) {0}" unfolding integer_mod_group_def by simp
  qed
qed

lemma Zn_cyclic_group:
  obtains x where "cyclic_group (Z n) x"
  using Z1_cyclic_group Zn_neq1_cyclic_group by metis

lemma Zn_order: "order (Z n) = n"
  by (unfold integer_mod_group_def integer_group_def order_def, auto)

lemma (in cyclic_group) Zn_iso:
  assumes "order G = n"
  shows "G \<cong> Z n"
  using Zn_order Zn_cyclic_group iso_cyclic_groups_same_order assms by metis

end