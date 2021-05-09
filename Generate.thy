theory Generate
  imports General_Groups "HOL-Algebra.Algebra"
begin

lemma (in group) generate_sincl:
  "A \<subseteq> generate G A"
  using generate.incl by fast

lemma (in group) generate_idem:
  assumes "A \<subseteq> carrier G"
  shows "generate G (generate G A) = generate G A"
  using assms generateI group.generate_is_subgroup by blast

lemma (in group) generate_idem':
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "generate G (generate G A \<union> B) = generate G (A \<union> B)"
proof
  show "generate G (generate G A \<union> B) \<subseteq> generate G (A \<union> B)"
  proof -
    have "generate G A \<union> B \<subseteq> generate G (A \<union> B)"
    proof -
      have "generate G A \<subseteq> generate G (A \<union> B)" using mono_generate by simp
      moreover have "B \<subseteq> generate G (A \<union> B)" by (simp add: generate.incl subset_iff)
      ultimately show ?thesis by simp
    qed
    then have "generate G (generate G A \<union> B) \<subseteq> generate G (generate G (A \<union> B))" using mono_generate by auto
    with generate_idem[of "A \<union> B"] show ?thesis using assms by simp
  qed
  show "generate G (A \<union> B) \<subseteq> generate G (generate G A \<union> B)"
  proof -
    have "A \<subseteq> generate G A" using generate.incl by fast
    thus ?thesis using mono_generate[of "A \<union> B" "generate G A \<union> B"] by blast
  qed
qed

lemma (in group) generate_subset_change_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G" "C \<subseteq> carrier G" "generate G A = generate G B"
  shows "generate G (A \<union> C) = generate G (B \<union> C)"
  by (metis assms generate_idem')

lemma (in group) generate_subgroup_id:
  assumes "subgroup H G"
  shows "generate G H = H"
  using assms generateI by auto

lemma (in group) generate_consistent':
  assumes "subgroup H G" "A \<subseteq> H"
  shows "\<forall>x \<in> A. generate G {x} = generate (G\<lparr>carrier := H\<rparr>) {x}"
  using generate_consistent assms by auto

lemma (in group) generate_idem_Un:
  assumes "A \<subseteq> carrier G"
  shows "generate G (\<Union>x\<in>A. generate G {x}) = generate G A"
proof
  have "A \<subseteq> (\<Union>x\<in>A. generate G {x})" using generate.incl by force
  thus "generate G A \<subseteq> generate G (\<Union>x\<in>A. generate G {x})" using mono_generate by presburger
  have "\<And>x. x \<in> A \<Longrightarrow> generate G {x} \<subseteq> generate G A" using mono_generate by auto
  then have "(\<Union>x\<in>A. generate G {x}) \<subseteq> generate G A" by blast
  thus "generate G (\<Union>x\<in>A. generate G {x}) \<subseteq> generate G A" using generate_idem[OF assms] mono_generate by blast
qed

lemma (in group) generate_idem_fUn:
  assumes "f A \<subseteq> carrier G"
  shows "generate G (\<Union> {generate G {x} |x. x \<in> f A}) = generate G (f A)"
proof
  have "f A \<subseteq> \<Union> {generate G {x} |x. x \<in> f A}"
  proof
    fix x
    assume x: "x \<in> f A"
    have "x \<in> generate G {x}" using generate.incl by fast
    thus "x \<in> \<Union> {generate G {x} |x. x \<in> f A}" using x by blast
  qed
  thus "generate G (f A) \<subseteq> generate G (\<Union> {generate G {x} |x. x \<in> f A})" using mono_generate by auto
  have "\<And>x. x \<in> f A \<Longrightarrow> generate G {x} \<subseteq> generate G (f A)" using mono_generate by simp
  then have "(\<Union> {generate G {x} |x. x \<in> f A}) \<subseteq> generate G (f A)" by blast
  with mono_generate[OF this] show "generate G (\<Union> {generate G {x} |x. x \<in> f A}) \<subseteq> generate G (f A)" using generate_idem[OF assms] by simp
qed

lemma (in group) generate_idem_fim_Un:
  assumes "\<Union>(f ` A) \<subseteq> carrier G"
  shows "generate G (\<Union>S \<in> A. generate G (f S)) = generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)})"
proof
  
  have "\<And>S. S \<in> A \<Longrightarrow> generate G (f S) = generate G (\<Union> {generate G {x} |x. x \<in> f S})" using generate_idem_fUn[of f] assms by blast
  then have "generate G (\<Union>S \<in> A. generate G (f S)) = generate G (\<Union>S \<in> A. generate G (\<Union> {generate G {x} |x. x \<in> f S}))" by simp

  have "\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)} \<subseteq> (\<Union>S\<in>A. generate G (f S))"
  proof
    fix x
    assume x: "x \<in> \<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}"
    then obtain a where a: "x \<in> generate G {a}" "a \<in> \<Union> (f ` A)" by blast
    then obtain M where M: "a \<in> f M" "M \<in> A" by blast
    then have "generate G {a} \<subseteq> generate G (f M)"
      using generate.incl[OF M(1), of G] mono_generate[of "{a}" "generate G (f M)"] generate_idem assms by auto
    then have "x \<in> generate G (f M)" using a by blast
    thus "x \<in> (\<Union>S\<in>A. generate G (f S))" using M by blast
  qed
  thus "generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}) \<subseteq> generate G (\<Union>S\<in>A. generate G (f S))" using mono_generate by simp
  have a: "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (\<Union> (f ` A))"
  proof -
    have "\<And>S. S \<in> A \<Longrightarrow> generate G (f S) \<subseteq> generate G (\<Union> (f ` A))" using mono_generate[of _ "\<Union> (f ` A)"] by blast
    then have "(\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (\<Union> (f ` A))" by blast
    then have "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (generate G (\<Union> (f ` A)))" using mono_generate by meson
    thus "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq>  generate G (\<Union> (f ` A))" using generate_idem assms by blast
  qed
  have "\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)} = (\<Union>x\<in>\<Union> (f ` A). generate G {x})" by blast
  with generate_idem_Un[OF assms] have "generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}) = generate G (\<Union> (f ` A))" by simp
  with a show "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)})" by blast
qed

lemma (in group) generate_singleton_one:
  assumes "generate G {a} = {\<one>}"
  shows "a = \<one>"
  using generate.incl[of a "{a}" G] assms by auto

lemma (in group) generate_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G" "A \<subseteq> generate G B" "B \<subseteq> generate G A"
  shows "generate G A = generate G B"
  by (meson assms generate_subgroup_incl group.generate_is_subgroup is_group order_class.order.antisym)

lemma (in group) generate_inv_eq:
  assumes "a \<in> carrier G"
  shows "generate G {a} = generate G {inv a}"
  by (intro generate_eqI; use assms generate.inv[of a] generate.inv[of "inv a" "{inv a}" G] inv_inv[OF assms] in auto)

lemma (in group) generate_eq_imp_subset:
  assumes "generate G A = generate G B"
  shows "A \<subseteq> generate G B"
  using generate.incl assms by fast

lemma (in group) generate_subset_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> A" "A - B \<subseteq> generate G B"
  shows "generate G A = generate G B"
proof
  show "generate G B \<subseteq> generate G A" by (intro mono_generate, fact)
  show "generate G A \<subseteq> generate G B"
  proof(subst generate_idem[of "B", symmetric])
    show "generate G A \<subseteq> generate G (generate G B)"
      by (intro mono_generate, use assms generate_sincl[of B] in auto)
  qed (use assms in blast)
qed

lemma (in group) generate_one_irrel:
  "generate G A = generate G (A \<union> {\<one>})"
proof
  show "generate G A \<subseteq> generate G (A \<union> {\<one>})" by (intro mono_generate, blast)
  show "generate G (A \<union> {\<one>}) \<subseteq> generate G A"
  proof
    fix x
    assume x: "x \<in> generate G (A \<union> {\<one>})"
    thus "x \<in> generate G A"
    proof(induction rule: generate.induct)
    case one
      then show ?case using generate.one by auto
    next
      case (incl h)
      then show ?case using generate.one generate.incl by fast
    next
      case (inv h)
      then show ?case using generate.one generate.inv by fastforce
    next
      case (eng h1 h2)
      then show ?case using generate.eng by fast
    qed
  qed
qed

lemma (in group) generate_one_irrel':
  "generate G A = generate G (A - {\<one>})"
proof
  show "generate G (A - {\<one>}) \<subseteq> generate G A" by (intro mono_generate, blast)
  show "generate G A \<subseteq> generate G (A - {\<one>})"
  proof
    fix x
    assume x: "x \<in> generate G A"
    thus "x \<in> generate G (A - {\<one>})"
    proof(induction rule: generate.induct)
    case one
      then show ?case using generate.one by auto
    next
      case i: (incl h)
      then show ?case
      proof(cases "h = \<one>")
        case True
        then show ?thesis using generate.one by blast
      next
        case False
        with i have "h \<in> (A - {\<one>})" by blast
        then show ?thesis using generate.incl by metis
      qed
    next
      case i: (inv h)
      then show ?case
      proof(cases "h = \<one>")
        case True
        then show ?thesis using generate.one by auto
      next
        case False
        with i have "h \<in> (A - {\<one>})" by blast
        then show ?thesis using generate.inv by metis
      qed
    next
      case (eng h1 h2)
      then show ?case using generate.eng by fast
    qed
  qed
qed

lemma (in group) generate_one_switched_eqI:
  assumes "A \<subseteq> carrier G" "a \<in> A" "B = (A - {a}) \<union> {b}"
  and "b \<in> generate G A" "a \<in> generate G B"
  shows "generate G A = generate G B"
proof
  have gAc: "generate G A \<subseteq> carrier G" by (intro generate_incl[OF assms(1)])
  hence Bc: "B \<subseteq> carrier G" using assms by blast
  show "generate G A \<subseteq> generate G B"
  proof(subst generate_idem[OF Bc, symmetric], intro mono_generate, rule)
    fix x
    assume x: "x \<in> A"
    show "x \<in> generate G B"
    proof (cases "x = a")
      case True
      then show ?thesis using assms by blast
    next
      case False
      with x assms have "x \<in> B" by blast
      thus ?thesis using generate.incl by metis
    qed
  qed
  show "generate G B \<subseteq> generate G A"
  proof(subst generate_idem[OF assms(1), symmetric], intro mono_generate, rule)
    fix x
    assume x: "x \<in> B"
    show "x \<in> generate G A"
    proof (cases "x = b")
      case True
      then show ?thesis using assms by blast
    next
      case False
      with x assms have "x \<in> A" by blast
      thus ?thesis using generate.incl by metis
    qed
  qed
qed

lemma (in group) generate_nat_pow:
  assumes "ord a \<noteq> 0" "a \<in> carrier G"
  shows "generate G {a} = {a [^] k |k. k \<in> {0..ord a - 1}}"
proof -
  obtain n where n: "n = ord a" "n > 0" using assms by blast
  have "\<And>m. a [^] m = a [^] (m mod int n)"
    using n pow_int_mod_ord assms assms(2) by blast
  moreover have "\<And>m. a [^] (m mod int n) \<in> {a [^] k |k::int. k \<in> {0..(int n) - 1}}"
    using pos_mod_conj[of n] n(2) by auto
  ultimately have gp:"\<And>m::int. a [^] m \<in> {a [^] k |k::int. k \<in> {0..(int n) - 1}}"
    by presburger
  then have 1:"generate G {a} = {a [^] k|k::int. k \<in> {0..(int n) - 1}}"
    using generate_pow[of a] assms(2) by auto
  have 2:"{a [^] k|k::int. k \<in> {0..(int n - 1)}} = {a [^] k|k::nat. k \<in> {0..n - 1}}" (is "?L = ?R")
  proof(intro equalityI subsetI)
    fix x
    assume "x \<in> ?L"
    then obtain k where k:"x = a [^] (k::int)" "0 \<le> k" "k < n" by auto
    then have "x = a [^] (nat k)" by auto
    moreover have "nat k \<in> {0..n-1}" using k by fastforce
    ultimately show "x \<in> ?R" by fast
  next
    fix x
    assume "x \<in> ?R"
    then obtain k where k:"x = a [^] (k::nat)" "k \<le> n" by force
    then have g: "x = a [^] (int k)" using int_pow_int[of G a k] by argo
    thus "x \<in> ?L"
    proof (cases "k = n")
      case True
      then have "x = \<one>" using n k assms(2) by auto
      then show ?thesis using gp by force
    next
      case False
      then have "int k \<in> {0::int..(int n - 1)}" using k by fastforce
      with g show ?thesis by blast
    qed
  qed
  show ?thesis using 1 2 n by algebra
qed

lemma (in group) generate_nat_pow':
  assumes "ord a \<noteq> 0" "a \<in> carrier G"
  shows "generate G {a} = {a [^] k |k. k \<in> {1..ord a}}"
proof -
  have "{a [^] k |k. k \<in> {1..ord a}} = {a [^] k |k. k \<in> {0..ord a - 1}}"
  proof -
    have "a [^] k \<in> {a [^] k |k. k \<in> {0..ord a - 1}}" if "k \<in> {1..ord a}" for k
      using that pow_nat_mod_ord[OF assms(2, 1), of "ord a"] assms by (cases "k = ord a"; force)
    moreover have "a [^] k \<in> {a [^] k |k. k \<in> {1..ord a}}" if "k \<in> {0..ord a - 1}" for k
    proof(cases "k = 0")
      case True
      hence "a [^] k = a [^] ord a" using pow_ord_eq_1[OF assms(2)] by auto
      moreover have "ord a \<in> {1..ord a}" using assms unfolding atLeastAtMost_def atLeast_def atMost_def by auto
      ultimately show ?thesis by blast
    next
      case False
      then show ?thesis using that by auto
    qed 
    ultimately show ?thesis by blast
  qed
  with generate_nat_pow[OF assms] show ?thesis by simp
qed

end