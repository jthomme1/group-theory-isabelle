theory IDirProds
  imports Generate Stuff
begin

definition IDirProd :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "IDirProd G Y Z = generate G (Y \<union> Z)"

definition IDirProds :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "IDirProds G Y = generate G (\<Union>Y)"

definition (in group) complementary_family :: "'a set set \<Rightarrow> bool" where
  "complementary_family Hs = (\<forall>H \<in> Hs. complementary H (IDirProds G (Hs - {H})))"

definition (in group) compl_gens :: "'a set \<Rightarrow> bool" where
  "compl_gens gs = (\<forall>g \<in> gs. complementary (generate G {g}) (generate G (gs - {g})))"

lemma (in group) compl_fam_empty[simp]: "complementary_family {}"
  unfolding complementary_family_def by simp

lemma (in group) compl_gens_empty[simp]: "compl_gens {}"
  unfolding compl_gens_def by simp

lemma (in group) compl_gens_subset:
  assumes "gs \<subseteq> carrier G" "compl_gens gs" "A \<subseteq> gs"
  shows "compl_gens A"
proof(unfold compl_gens_def, rule)
  fix g
  assume g: "g \<in> A"
  have "generate G (A - {g}) \<subseteq> generate G (gs - {g})" by (intro mono_generate, use assms(3) in auto)
  from subgroup_subset_complementary[OF generate_is_subgroup generate_is_subgroup generate_is_subgroup this, of "{g}"]
  show "complementary (generate G {g}) (generate G (A - {g}))" using g assms unfolding compl_gens_def by blast
qed

lemma (in group) compl_gens_comp_fam_gen_same:
  assumes "gs \<subseteq> carrier G"
  shows "IDirProds G ((\<lambda>g. generate G {g}) ` gs) = generate G gs"
proof
  let ?gen = "(\<lambda>g. generate G g)"
  let ?gens = "(\<lambda>g. generate G {g})"
  show "IDirProds G ((\<lambda>g. generate G {g}) ` gs) \<subseteq> generate G gs" unfolding IDirProds_def
  proof -
    have "?gen (\<Union> (?gens ` gs)) \<subseteq> ?gen (?gen gs)"
    proof(intro mono_generate)
      have "?gens g \<subseteq> ?gen gs" if "g \<in> gs" for g by (intro mono_generate, use that in blast)
      thus "(\<Union>g\<in>gs. ?gens g) \<subseteq> ?gen gs" by blast
    qed
    also have "\<dots> = ?gen gs" by(intro generate_idem, use assms in blast)
    finally show "?gen (\<Union> (?gens ` gs)) \<subseteq> ?gen gs" .
  qed
  show "generate G gs \<subseteq> IDirProds G ((\<lambda>g. generate G {g}) ` gs)" unfolding IDirProds_def
    by (intro mono_generate, use generate.incl in force)
qed
  
lemma (in group) compl_gens_imp_complementary_family:
  assumes "gs \<subseteq> carrier G" "compl_gens gs"
  shows "complementary_family ((\<lambda>g. generate G {g}) ` gs)"
proof (unfold complementary_family_def, rule)
  let ?gen = "(\<lambda>g. generate G g)"
  let ?gens = "(\<lambda>g. generate G {g})"
  fix H
  assume H: "H \<in> ?gens ` gs"
  then obtain g where g: "g \<in> gs" "H = ?gens g" by blast
  with assms(2) have c: "complementary (?gens g) (?gen (gs - {g}))" unfolding compl_gens_def by blast
  have subs: "?gen (\<Union> (?gens ` gs - {H})) \<subseteq> ?gen (gs - {g})"
  proof(subst g(2))
    have "?gen (\<Union> (?gens ` gs - {?gens g})) \<subseteq> ?gen (\<Union>(?gens ` (gs - {g})))" by (intro mono_generate, blast)
    also have "\<dots> \<subseteq> ?gen (?gen (gs - {g}))"
    proof(intro mono_generate)
      have "?gens h \<subseteq> ?gen (gs - {g})" if "h \<in> gs - {g}" for h by (intro mono_generate, use that in blast)
      thus "(\<Union>g\<in>gs - {g}. ?gens g) \<subseteq> ?gen (gs - {g})" by blast
    qed
    also have "\<dots> = ?gen (gs - {g})" by(intro generate_idem, use assms(1) in blast)
    finally show "?gen (\<Union> (?gens ` gs - {?gens g})) \<subseteq> ?gen (gs - {g})" .
  qed
  show "complementary H (IDirProds G ((\<lambda>g. generate G {g}) ` gs - {H}))"
  proof(unfold IDirProds_def, subst g(2), intro subgroup_subset_complementary[OF generate_is_subgroup[of "{g}"] generate_is_subgroup generate_is_subgroup subs c])
    show "{g} \<subseteq> carrier G" "gs - {g} \<subseteq> carrier G" using assms(1) g(1) by blast+
    have "generate G {g} \<subseteq> carrier G" if "g \<in> gs" for g by (intro generate_incl, use that assms(1) in blast)
    thus "\<Union> ((\<lambda>g. generate G {g}) ` gs - {H}) \<subseteq> carrier G" by blast
  qed
qed

lemma (in group) compl_gens_imp_generate_inj:
  assumes "gs \<subseteq> carrier G" "compl_gens gs"
  shows "inj_on (\<lambda>g. generate G {g}) gs"
proof(rule, rule ccontr)
  fix x y
  assume xy: "x \<in> gs" "y \<in> gs" "x \<noteq> y"
  assume g: "generate G {x} = generate G {y}"
  with xy have "generate G {y} \<subseteq> generate G (gs - {y})" using mono_generate[of "{x}" "gs - {y}"] by auto
  with xy have gyo: "generate G {y} = {\<one>}" using assms(2)[unfolded compl_gens_def complementary_def] generate.one by blast
  hence yo: "y = \<one>" using generate_singleton_one by simp
  from gyo g generate_singleton_one have xo: "x = \<one>" by simp
  from xy yo xo show False by blast
qed

inductive (in group) is_idirprod :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "(\<And>H. H \<in> B \<Longrightarrow> H \<lhd> G) \<Longrightarrow>
   A = IDirProds G B \<Longrightarrow>
   complementary_family B \<Longrightarrow>
   is_idirprod A B"

lemma (in comm_group) is_idirprod_subgroup_suffices:
  assumes "carrier G = IDirProds G Hs"
  and "finite Hs" "\<And>H. H \<in> Hs \<Longrightarrow> subgroup H G" "complementary_family Hs"
  shows "is_idirprod (carrier G) Hs"
  by(intro is_idirprod.intros, use assms subgroup_imp_normal in auto)

inductive (in group) is_idirgen :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "(\<And>g. g \<in> gs \<Longrightarrow> (generate G {g}) \<lhd> G) \<Longrightarrow>
   A = generate G gs \<Longrightarrow>
   compl_gens gs \<Longrightarrow>
   is_idirgen A gs"

lemma (in comm_group) is_idirgen_self:
  assumes "gs \<subseteq> carrier G" "compl_gens gs"
  shows "is_idirgen (generate G gs) gs"
proof
  show "generate G {g} \<lhd> G" if "g \<in> gs" for g using subgroup_imp_normal[OF generate_is_subgroup[of "{g}"]] assms that by auto
  show "compl_gens gs" by fact
qed simp

lemma (in group) idirgen_imp_idirprod:
  assumes "is_idirgen A gs" "gs \<subseteq> carrier G"
  shows "is_idirprod A ((\<lambda>g. generate G {g}) ` gs)"
proof
  from assms(1) is_idirgen.simps[of A gs] have a: "\<forall>x. x \<in> gs \<longrightarrow> generate G {x} \<lhd> G" "A = generate G gs" "compl_gens gs" by blast+
  thus "\<And>H. H \<in> (\<lambda>g. generate G {g}) ` gs \<Longrightarrow> H \<lhd> G" by blast
  from compl_gens_imp_complementary_family[OF assms(2) a(3)] show "complementary_family ((\<lambda>g. generate G {g}) ` gs)" .
  show "A = IDirProds G ((\<lambda>g. generate G {g}) ` gs)" using compl_gens_comp_fam_gen_same[OF assms(2)] a(2) by blast
qed

(* lemmas to IDirProd and IDirProds *)

lemma (in group) IDirProd_one_right:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G A {\<one>} = generate G A"
  unfolding IDirProd_def
proof
  interpret sA: subgroup "(generate G A)" G using assms generate_is_subgroup by simp
  interpret sAone: subgroup "(generate G (A \<union> {\<one>}))" G using assms generate_is_subgroup by simp
  show "generate G (A \<union> {\<one>}) \<subseteq> generate G A"
    using generate_subgroup_incl[of "A \<union> {\<one>}" "generate G A"] generate.incl assms sA.one_closed sA.subgroup_axioms by fast
  show "generate G A \<subseteq> generate G (A \<union> {\<one>})"
    using mono_generate[of A "A \<union> {\<one>}"] by blast
qed

lemma (in group) IDirProds_incl:
  assumes "A \<in> S"
  shows "A \<subseteq> IDirProds G S"
  unfolding IDirProds_def using assms generate.incl[of _ "\<Union>S" G] by blast

lemma (in group) IDirProd_one_left:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G {\<one>} A = generate G A"
  using IDirProd_one_right[of A] assms unfolding IDirProd_def by force

lemma (in group) IDirProd_empty_right:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G A {} = generate G A"
  unfolding IDirProd_def by simp

lemma (in group) IDirProd_empty_left:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G {} A = generate G A"
  unfolding IDirProd_def by simp

lemma (in group) IDirProd_is_subgroup:
  assumes "Y \<subseteq> carrier G" "Z \<subseteq> carrier G"
  shows "subgroup (IDirProd G Y Z) G"
  unfolding IDirProd_def using generate_is_subgroup[of "Y \<union> Z"] assms by simp

lemma (in group) IDirProds_empty:
  "IDirProds G {} = {\<one>}"
  unfolding IDirProds_def using generate_empty by simp

lemma (in group) IDirProds_is_subgroup:
  assumes "\<Union>Y \<subseteq> (carrier G)"
  shows "subgroup (IDirProds G Y) G"
  unfolding IDirProds_def using generate_is_subgroup[of "\<Union>Y"] assms by auto

lemma (in group) IDirProd_comm:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "IDirProd G A B = IDirProd G B A"
  unfolding IDirProd_def by (simp add: sup_commute)

lemma (in group) IDirProds_idem:
  assumes "\<Union>A \<subseteq> carrier G"
  shows "IDirProds G {(IDirProds G A)} = IDirProds G A"
  unfolding IDirProds_def using generate_idem[OF assms] by simp
lemma (in group) generate_idem'_right:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "generate G (A \<union> generate G B) = generate G (A \<union> B)"
  using generate_idem'[OF assms(2) assms(1)] by (simp add: sup_commute)

lemma (in group) IDirProds_in_IDirProd:
  assumes "A \<subseteq> carrier G" "\<Union>Y \<subseteq> carrier G"
  shows "IDirProd G A (IDirProds G Y) = IDirProds G (insert A Y)"
  unfolding IDirProd_def IDirProds_def
proof -
  have "generate G (A \<union> generate G (\<Union> Y)) = generate G (generate G (\<Union> Y) \<union> A)" by (simp add: sup_commute)
  also have "\<dots> = generate G (\<Union> Y \<union> A)" by (rule generate_idem'[OF assms(2) assms(1)])
  also have "\<dots> = generate G (\<Union> (insert A Y))" by (simp add: Un_commute)
  finally show "generate G (A \<union> generate G (\<Union> Y)) = generate G (\<Union> (insert A Y))" .
qed

lemma (in comm_group) IDirProd_eq_subgroup_mult:
  assumes "subgroup H G" "subgroup J G"
  shows "IDirProd G H J = H <#> J"
  unfolding IDirProd_def
  by (rule generate_subgroup_eq_set_mult[OF assms])

lemma (in group) IDirProds_subgroup_id: "subgroup H G \<Longrightarrow> IDirProds G {H} = H" (* Manuel *)
  by (simp add: generate_subgroup_id IDirProds_def)

lemma (in comm_group) IDirProds_Un: (* Manuel *)
  assumes "\<forall>H\<in>A. subgroup H G" "\<forall>H\<in>B. subgroup H G"
  shows   "IDirProds G (A \<union> B) = IDirProds G A <#> IDirProds G B"
proof -
  have subset: "\<Union> A \<subseteq> carrier G" "\<Union> B \<subseteq> carrier G"
    using subgroup.subset assms(1, 2) by blast+
  have "IDirProds G A <#> IDirProds G B = IDirProd G (IDirProds G A) (IDirProds G B)"
    using assms by (intro IDirProd_eq_subgroup_mult [symmetric] IDirProds_is_subgroup subset)
  also have "\<dots> = generate G (\<Union> A \<union> IDirProds G B)"
    unfolding IDirProds_def IDirProd_def by (intro generate_idem' generate_incl subset)
  also have "\<dots> = generate G (\<Union>A \<union> \<Union>B)"
    unfolding IDirProds_def IDirProd_def
    by (intro generate_idem'_right generate_incl subset)
  also have "\<Union>A \<union> \<Union>B = \<Union>(A \<union> B)"
    by blast
  also have "generate G \<dots> = IDirProds G (A \<union> B)"
    unfolding IDirProds_def ..
  finally show ?thesis ..
qed

lemma (in comm_group) IDirProds_finite:
  assumes "finite S" "\<forall>P\<in>S. subgroup P G" "\<forall>P\<in>S. finite P"
  shows "finite (IDirProds G S)" using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case using IDirProds_empty by simp
next
  case i: (insert x F)
  have sx: "subgroup x G" using i by blast
  then have cx: "x \<subseteq> carrier G" using subgroup.subset by blast
  have cF: "\<Union>F \<subseteq> carrier G" using i subgroup.subset by blast
  have sF: "subgroup (IDirProds G F) G" using IDirProds_is_subgroup[OF cF] .
  then have cFI: "(IDirProds G F) \<subseteq> carrier G" using subgroup.subset by blast
  from i have f: "finite x" "finite (IDirProds G F)" "finite {x}" by blast+
  from IDirProds_Un have "IDirProds G ({x} \<union> F) = IDirProds G {x} <#> IDirProds G F" using i by blast
  also have "\<dots> = x <#> IDirProds G F" using IDirProds_subgroup_id[OF sx] by simp
  also have "finite (\<dots>)" using set_mult_finite[OF f(1, 2) cx cFI] .
  finally show ?case unfolding insert_def by simp
qed

lemma (in comm_group) IDirProds_compl_imp_compl:
  assumes "\<And>J. J \<in> H \<Longrightarrow> subgroup J G" and "subgroup H1 G"
  assumes "complementary H1 (IDirProds G H)" "H2 \<in> H"
  shows   "complementary H1 H2" unfolding complementary_def
proof -
  have "H2 \<subseteq> IDirProds G H" using assms
    by (metis IDirProds_def UnionI generate.incl subsetI)
  then have "H1 \<inter> H2 \<subseteq> H1 \<inter> IDirProds G H" by blast
  moreover have "\<one> \<in> H1 \<inter> H2" using subgroup.one_closed assms by auto
  ultimately show "H1 \<inter> H2 = {\<one>}" using assms(3) unfolding complementary_def by blast
qed

lemma (in comm_group) finite_sub_card_eq_mult_imp_comp:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  and "card (IDirProd G H J) = (card J * card H)"
  shows "complementary H J"
  unfolding complementary_def
proof (rule ccontr)
  assume "H \<inter> J \<noteq> {\<one>}"
  have "\<one> \<in> H" using subgroup.one_closed assms(1) by blast
  moreover have "\<one> \<in> J" using subgroup.one_closed assms(2) by blast
  ultimately have "\<one> \<in> (H \<inter> J)" by blast

  then obtain a where a_def: "a \<in> (H \<inter> J) \<and> a \<noteq> \<one>" using \<open>H \<inter> J \<noteq> {\<one>}\<close> by blast
  then have aH: "a \<in> H" by blast
  then have a_inv_H: "inv a \<in> H \<and> inv a \<noteq> \<one>" using assms(1) by (meson a_def inv_eq_1_iff subgroup.mem_carrier subgroupE(3))
  from a_def have aJ: "a \<in> J" by blast
  then have a_inv_J: "inv a \<in> J \<and> inv a \<noteq> \<one>" using assms(2) by (meson a_def inv_eq_1_iff subgroup.mem_carrier subgroupE(3))
  from a_def have a_c: "a \<in> carrier G" using subgroup.subset[of J G] assms(2) by blast

  from generate_subgroup_eq_set_mult[of H J] have eq_m: "IDirProd G H J = H <#> J" using IDirProd_def[of G H J] assms by argo
  with set_mult_card_eq_impl_empty_inter'[of H J] have empty: "\<And>a b.\<lbrakk>a \<in> H; b \<in> H; a \<noteq> b\<rbrakk> \<Longrightarrow> (l_coset G a J) \<inter> (l_coset G b J) = {}"
    using assms subgroup.subset[of _ G] by simp

  have "\<one> \<in> \<one> <# J" using \<open>\<one> \<in> J\<close> unfolding l_coset_def by force
  moreover have "\<one> \<in> a <# J" using a_inv_J aJ a_c assms \<open>\<one> \<in> J\<close> coset_join3 by blast
  ultimately have "(l_coset G \<one> J) \<inter> (l_coset G a J) \<noteq> {}" by blast

  then show "False" using empty[of "\<one>" a] a_def aH \<open>\<one> \<in> H\<close> by blast
qed

lemma (in comm_group) finite_sub_comp_imp_card_eq_mult:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  and "complementary H J"
shows "card (IDirProd G H J) = card J * card H"
  unfolding IDirProd_eq_subgroup_mult[OF assms(1, 2)]
proof -
  have carr: "H \<subseteq> carrier G" "J \<subseteq> carrier G" using assms subgroup.subset by auto

  from coset_neq_imp_empty_inter[OF assms(1)] compl_imp_diff_cosets[OF assms(1,2)]
  have em_inter: "\<And>a b. \<lbrakk>a \<in> J; b \<in> J; a \<noteq> b\<rbrakk> \<Longrightarrow> (H #> a) \<inter> (H #> b) = {}"
    by (meson assms subgroup.mem_carrier)

  have "card (\<Union>a\<in>J. (H #> a)) = card J * card H" using assms(4) carr(2) em_inter
  proof (induction J rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case i: (insert x F)
    then have cF:"card (\<Union> ((#>) H ` F)) = card F * card H" by blast
    have xc[simp]: "x \<in> carrier G" using i(4) by simp
    let ?J = "insert x F"
    from i(2, 4, 5) have em:"(H #> x) \<inter> (\<Union>y\<in>F. (H #> y)) = {}" by auto
    have "finite (H #> x)"
      by (meson carr(1) rcosetsI rcosets_finite assms(3) xc)
    moreover have "finite (H <#> F)" using set_mult_finite[OF assms(3) i(1) carr(1)] i(4) by blast
    moreover have "H <#> F = (\<Union>a\<in>F. (H #> a))" unfolding set_mult_def using r_coset_def[of G H] by auto
    ultimately have "card(H #> x) + card(\<Union>y\<in>F. (H #> y)) = card((H #> x) \<union> (\<Union>y\<in>F. (H #> y))) + card((H #> x) \<inter> (\<Union>y\<in>F. (H #> y)))"
      using card_Un_Int by auto
    then have "card(H #> x) + card(\<Union>y\<in>F. (H #> y)) = card((H #> x) \<union> (\<Union>y\<in>F. (H #> y)))"
      using i(5) em by simp
    moreover have "card (H #> x) = card H"
      using card_rcosets_equal[of _ H] rcosetsI[of H] carr(1) xc by metis
    moreover have "card (insert x F) * card H = card F * card H + card H" by (simp add: i.hyps(1) i(2))
    ultimately show ?case using cF by simp
  qed
  moreover have "H <#> J = (\<Union>a\<in>J. (H #> a))" unfolding set_mult_def using r_coset_def[of G H] by auto
  ultimately show "card (H <#> J) = card J * card H" by argo
qed

lemma (in comm_group) finite_sub_comp_iff_card_eq_mult:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  shows "card (IDirProd G H J) = card J * card H  \<longleftrightarrow> complementary H J"
  using finite_sub_comp_imp_card_eq_mult[OF assms] finite_sub_card_eq_mult_imp_comp[OF assms]
  by blast

lemma (in comm_group) IDirProds_card:
  assumes "finite S" "\<forall>P\<in>S. subgroup P G" "\<forall>P\<in>S. finite P" "pairwise (\<lambda>x y. coprime (card x) (card y)) S"
  shows "card (IDirProds G S) = (\<Prod>P \<in> S. card P)" using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case using IDirProds_empty by simp
next
  case i: (insert x F)
  have sx: "subgroup x G" using i(4) by blast
  have cx: "x \<subseteq> carrier G" using subgroup.subset[OF sx] .
  have fx: "finite x" using i by blast
  have cF: "\<Union>F \<subseteq> carrier G" using subgroup.subset[of _ G] i(4) by blast
  from generate_is_subgroup[OF this] have sFI: "subgroup (IDirProds G F) G" unfolding IDirProds_def .
  then have cFI: "(IDirProds G F) \<subseteq> carrier G" using subgroup.subset by blast
  have fFI: "finite (IDirProds G F)" using IDirProds_finite[OF i(1)] i by blast

  from i have ih: "card (IDirProds G F) = prod card F" unfolding pairwise_def by blast
  have cop: "coprime (card (IDirProds G F)) (card x)"
  proof -
    have cFI0: "card (IDirProds G F) \<noteq> 0" using finite_subgroup_card_neq_0[OF sFI fFI] .
    moreover have cx0: "card x \<noteq> 0" using finite_subgroup_card_neq_0[OF sx fx] .
    moreover have  "prime_factors (card (IDirProds G F)) \<inter> prime_factors (card x) = {}"
    proof (rule ccontr)
      have n0: "\<And>P. P \<in> F \<Longrightarrow> card P \<noteq> 0" using finite_subgroup_card_neq_0 i(4, 5) by blast
      assume "prime_factors (card (IDirProds G F)) \<inter> prime_factors (card x) \<noteq> {}"
      moreover have "prime_factors (card (IDirProds G F)) = \<Union>(prime_factors ` card ` F)"
        using n0 prime_factors_Prod[OF i(1), of card] by (subst ih; simp)
      moreover have "\<And>P. P \<in> F \<Longrightarrow> prime_factors (card P) \<inter> prime_factors (card x) = {}"
      proof -
        fix P
        assume P: "P \<in> F"
        then have coPx: "coprime (card P) (card x)" using i(2, 6) unfolding pairwise_def by auto
        have "card P \<noteq> 0" using n0 P by blast
        from coprime_eq_empty_prime_inter[OF this cx0] show "prime_factors (card P) \<inter> prime_factors (card x) = {}"
          using coPx by blast
      qed
      ultimately show "False" by auto
    qed
    ultimately show ?thesis using coprime_eq_empty_prime_inter by blast
  qed
  from finite_sub_comp_imp_card_eq_mult[OF sFI sx fFI fx subgroups_order_coprime_imp_compl[OF sFI sx this]]
  have "card (IDirProd G (IDirProds G F) x) = card x * card (IDirProds G F)" .
  then have "card (IDirProds G (insert x F)) = card x * card (IDirProds G F)"
    using IDirProds_in_IDirProd[OF cx cF] IDirProd_comm[OF cx cFI] by argo
  also have "\<dots> = card x * prod card F" using ih by presburger
  also have "\<dots> = prod card ({x} \<union> F)" using i.hyps by auto
  finally show ?case by simp
qed

end