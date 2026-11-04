module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.PullbackBranch
import all StacksFrontier.AlgebraicGeometry.Etale.SupportedSections.PullbackBranch

/-!
# The canonical bijection of sections with closed support

For an étale map `U' ⟶ U` of the small étale site and a closed subscheme `Z'` of `U'` whose
image in `U` is closed, a section over `U` supported on the image is cut down to a section over
`U'` supported on `Z'`, and conversely a section over `U'` supported on `Z'` is extended to a
section over `U`. Supported sections are determined by their restriction to the selected
branch, so the two constructions are mutually inverse; this is
`AlgebraicGeometry.SmallEtale.supportedSectionsEquiv` (Stacks 0F6F).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- A section restricts to zero on the open complement of a closed set `R` iff its support lies in
`R`. -/
private theorem restrict_compl_eq_zero_iff_supportSection_subset
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U : SmallEtale B S hS) (R : Set ((SmallEtale.toScheme B S hS).obj U)) (hR : IsClosed R)
    (x : F.obj.obj (op U)) :
    F.obj.map (openObjectι B S hS U ⟨Rᶜ, hR.isOpen_compl⟩).op x = 0 ↔
      supportSection B S hS F U x ⊆ R := by
  rw [map_eq_zero_iff_range_subset_zeroOpen, openObjectι_range]
  exact Set.compl_subset_comm

/-- A morphism factoring through the inclusion of a Zariski open lands in that open. -/
private theorem comp_openObjectι_base_mem
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : SmallEtale B S hS) (O : ((SmallEtale.toScheme B S hS).obj X).Opens)
    {W : SmallEtale B S hS} (c : W ⟶ openObject B S hS X O)
    (y : (SmallEtale.toScheme B S hS).obj W) :
    ((SmallEtale.toScheme B S hS).map (c ≫ openObjectι B S hS X O)).base y ∈ (O : Set _) :=
  (openObjectι_range B S hS X O).le ⟨((SmallEtale.toScheme B S hS).map c).base y, rfl⟩

/-- Sections supported in a closed set `R` are determined by their restriction along an étale
map whose image contains `R`. -/
private theorem eq_of_supportSection_subset_of_restrict_eq
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U W : SmallEtale B S hS) (f : W ⟶ U) (R : Set ((SmallEtale.toScheme B S hS).obj U))
    (hR : IsClosed R) (hf : R ⊆ Set.range ((SmallEtale.toScheme B S hS).map f).base)
    (s t : F.obj.obj (op U)) (hs : supportSection B S hS F U s ⊆ R)
    (ht : supportSection B S hS F U t ⊆ R) (h : F.obj.map f.op s = F.obj.map f.op t) :
    s = t := by
  let C : ((SmallEtale.toScheme B S hS).obj U).Opens := ⟨Rᶜ, hR.isOpen_compl⟩
  let V : ULift.{u + 1} Bool → SmallEtale B S hS := fun b =>
    match b.down with | false => W | true => openObject B S hS U C
  let p : ∀ b, V b ⟶ U := fun b =>
    match b with | ULift.up false => f | ULift.up true => openObjectι B S hS U C
  have hcover : ∀ x, ∃ b y, ((SmallEtale.toScheme B S hS).map (p b)).base y = x := by
    intro x
    by_cases hx : x ∈ R
    · obtain ⟨y, hy⟩ := hf hx
      exact ⟨ULift.up false, y, hy⟩
    · obtain ⟨y, hy⟩ := (openObjectι_range B S hS U C).ge hx
      exact ⟨ULift.up true, y, hy⟩
  apply section_eq_of_restrict_eq_on_cover B S hS F V p hcover
    (fun b => etale_toScheme_map B S hS (p b)) s t
  rintro ⟨_ | _⟩
  · exact h
  · exact ((restrict_compl_eq_zero_iff_supportSection_subset B S hS F U R hR s).mpr hs).trans
      ((restrict_compl_eq_zero_iff_supportSection_subset B S hS F U R hR t).mpr ht).symm

/-- Sections of `W` that are compatible over `U` and vanish where they meet the complement of the
closed set `R` extend to a section over `U` supported in `R`. -/
private theorem exists_supportSection_subset_of_compatible_restrict
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U W : SmallEtale B S hS) (f : W ⟶ U) (R : Set ((SmallEtale.toScheme B S hS).obj U))
    (hR : IsClosed R) (hf : R ⊆ Set.range ((SmallEtale.toScheme B S hS).map f).base)
    (σ : F.obj.obj (op W))
    (hσ : ∀ {Y : SmallEtale B S hS} (a b : Y ⟶ W), a ≫ f = b ≫ f →
      F.obj.map a.op σ = F.obj.map b.op σ)
    (hσ0 : ∀ {Y : SmallEtale B S hS} (a : Y ⟶ W)
      (b : Y ⟶ openObject B S hS U ⟨Rᶜ, hR.isOpen_compl⟩),
      a ≫ f = b ≫ openObjectι B S hS U ⟨Rᶜ, hR.isOpen_compl⟩ → F.obj.map a.op σ = 0) :
    ∃ s : F.obj.obj (op U), supportSection B S hS F U s ⊆ R ∧ F.obj.map f.op s = σ := by
  let C : ((SmallEtale.toScheme B S hS).obj U).Opens := ⟨Rᶜ, hR.isOpen_compl⟩
  let V : ULift.{u + 1} Bool → SmallEtale B S hS := fun b =>
    match b.down with | false => W | true => openObject B S hS U C
  let p : ∀ b, V b ⟶ U := fun b =>
    match b with | ULift.up false => f | ULift.up true => openObjectι B S hS U C
  let localSection : ∀ b, F.obj.obj (op (V b)) := fun b =>
    match b with | ULift.up false => σ | ULift.up true => 0
  have hcover : ∀ x, ∃ b y, ((SmallEtale.toScheme B S hS).map (p b)).base y = x := by
    intro x
    by_cases hx : x ∈ R
    · obtain ⟨y, hy⟩ := hf hx
      exact ⟨ULift.up false, y, hy⟩
    · obtain ⟨y, hy⟩ := (openObjectι_range B S hS U C).ge hx
      exact ⟨ULift.up true, y, hy⟩
  have hgen := smallEtale_cover_of_jointlySurjective_etale B S hS (X := U)
    (I := ULift.{u + 1} Bool) V p hcover fun b => etale_toScheme_map B S hS (p b)
  have hcompat : ∀ {Y : SmallEtale B S hS} (b₁ b₂ : ULift.{u + 1} Bool)
      (a : Y ⟶ V b₁) (b : Y ⟶ V b₂), a ≫ p b₁ = b ≫ p b₂ →
        F.obj.map a.op (localSection b₁) = F.obj.map b.op (localSection b₂) := by
    rintro Y ⟨b₁⟩ ⟨b₂⟩ a b hab
    cases b₁ <;> cases b₂
    · exact hσ a b hab
    · simpa [localSection] using hσ0 a b hab
    · simpa [localSection] using (hσ0 b a hab.symm).symm
    · simp [localSection]
  obtain ⟨s, hsrestr⟩ := section_exists_of_compatible_cover B S hS F V p hgen localSection hcompat
  refine ⟨s, ?_, hsrestr (ULift.up false)⟩
  exact (restrict_compl_eq_zero_iff_supportSection_subset B S hS F U R hR s).mp
    (by simpa [localSection] using hsrestr (ULift.up true))


private theorem supportedSection_restrict_eq_on_branch_overlap
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (X U : SmallEtale B S hS) (q : X ⟶ U) (hq : Etale ((SmallEtale.toScheme B S hS).map q))
    (Z : Scheme.{u}) (i : Z ⟶ (SmallEtale.toScheme B S hS).obj X)
    [IsClosedImmersion i] [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map q)]
    (O : ((SmallEtale.toScheme B S hS).obj X).Opens)
    (hbranch : (O : Set ((SmallEtale.toScheme B S hS).obj X)) ∩
        ((SmallEtale.toScheme B S hS).map q).base ⁻¹'
          Set.range ((i ≫ (SmallEtale.toScheme B S hS).map q).base) = Set.range i.base)
    (s : F.obj.obj (op X))
    (hs : supportSection B S hS F X s ⊆ Set.range i.base)
    (W : SmallEtale B S hS) (a b : W ⟶ openObject B S hS X O)
    (hab : a ≫ openObjectι B S hS X O ≫ q =
      b ≫ openObjectι B S hS X O ≫ q) :
    F.obj.map (a ≫ openObjectι B S hS X O).op s =
      F.obj.map (b ≫ openObjectι B S hS X O).op s := by
  classical
  let jO := openObjectι B S hS X O
  let a' := a ≫ jO
  let b' := b ≫ jO
  let aS := (SmallEtale.toScheme B S hS).map a'
  let bS := (SmallEtale.toScheme B S hS).map b'
  let qS := (SmallEtale.toScheme B S hS).map q
  let iS := i
  let gS := i ≫ qS
  let A : Set ((SmallEtale.toScheme B S hS).obj W) := aS.base ⁻¹' Set.range iS.base
  let D : Set ((SmallEtale.toScheme B S hS).obj W) := bS.base ⁻¹' Set.range iS.base
  have hAclosed : IsClosed A :=
    (IsClosedImmersion.isClosedEmbedding iS).isClosed_range.preimage aS.continuous
  have hDclosed : IsClosed D :=
    (IsClosedImmersion.isClosedEmbedding iS).isClosed_range.preimage bS.continuous
  let N : ((SmallEtale.toScheme B S hS).obj W).Opens :=
    ⟨(A ∪ D)ᶜ, (hAclosed.union hDclosed).isOpen_compl⟩
  have hmap : aS ≫ qS = bS ≫ qS := by
    show (SmallEtale.toScheme B S hS).map (a' ≫ q) =
      (SmallEtale.toScheme B S hS).map (b' ≫ q)
    exact congrArg (SmallEtale.toScheme B S hS).map (by simpa [a', b', jO] using hab)
  let k := pullback.lift aS bS hmap
  have hdiag : IsOpenImmersion (pullback.diagonal qS) :=
    AlgebraicGeometry.Unramified.section_isOpenImmersion _ _ (pullback.diagonal_fst qS)
  let E : ((SmallEtale.toScheme B S hS).obj W).Opens :=
    ⟨k.base ⁻¹' Set.range (pullback.diagonal qS).base,
      hdiag.isOpen_range.preimage k.continuous⟩
  have haO : ∀ x, aS.base x ∈ (O : Set ((SmallEtale.toScheme B S hS).obj X)) :=
    comp_openObjectι_base_mem B S hS X O a
  have hbO : ∀ x, bS.base x ∈ (O : Set ((SmallEtale.toScheme B S hS).obj X)) :=
    comp_openObjectι_base_mem B S hS X O b
  have hAE : A ⊆ (E : Set _) := by
    intro x hx
    change aS.base x ∈ Set.range iS.base at hx
    exact pullback_point_in_diagonal_of_mem_closed_branch qS iS gS
      rfl O hbranch aS bS haO hbO hmap x hx
  have hDE : D ⊆ (E : Set _) := by
    intro x hx
    change bS.base x ∈ Set.range iS.base at hx
    obtain ⟨z, hz⟩ := hx
    have hqax : qS.base (aS.base x) = gS.base z := by
      calc
        qS.base (aS.base x) = qS.base (bS.base x) := by
          simpa only [← Scheme.Hom.comp_apply] using
            congrArg (fun f : (SmallEtale.toScheme B S hS).obj W ⟶
              (SmallEtale.toScheme B S hS).obj U => f.base x) hmap
        _ = qS.base (iS.base z) := congrArg qS.base hz.symm
        _ = gS.base z := by rfl
    have haxi : aS.base x ∈ Set.range iS.base := by
      have h : aS.base x ∈ (O : Set _) ∩ qS.base ⁻¹' Set.range gS.base :=
        ⟨haO x, z, hqax.symm⟩
      rwa [hbranch] at h
    exact pullback_point_in_diagonal_of_mem_closed_branch qS iS gS
      rfl O hbranch aS bS haO hbO hmap x haxi
  let VE := openObject B S hS W E
  let VN := openObject B S hS W N
  let jE := openObjectι B S hS W E
  let jN := openObjectι B S hS W N
  let V : ULift.{u + 1} Bool → SmallEtale B S hS := fun b =>
    match b with | ULift.up false => VE | ULift.up true => VN
  let p : ∀ b, V b ⟶ W := fun b =>
    match b with | ULift.up false => jE | ULift.up true => jN
  have hcov : ∀ x : (SmallEtale.toScheme B S hS).obj W,
      ∃ b y, ((SmallEtale.toScheme B S hS).map (p b)).base y = x := by
    intro x
    by_cases hx : x ∈ A ∪ D
    · obtain ⟨y, hy⟩ := (openObjectι_range B S hS W E).ge (Set.union_subset hAE hDE hx)
      exact ⟨ULift.up false, y, hy⟩
    · obtain ⟨y, hy⟩ := (openObjectι_range B S hS W N).ge hx
      exact ⟨ULift.up true, y, hy⟩
  have hetale : ∀ b, Etale ((SmallEtale.toScheme B S hS).map (p b)) := fun b =>
    etale_toScheme_map B S hS (p b)
  let sa := F.obj.map a'.op s
  let sb := F.obj.map b'.op s
  have hrestrE : F.obj.map jE.op sa = F.obj.map jE.op sb := by
    have hsub : Set.range (((SmallEtale.toScheme B S hS).map jE ≫ k).base) ⊆
        Set.range (pullback.diagonal qS).base := by
      rintro _ ⟨x, rfl⟩
      have hxE : ((SmallEtale.toScheme B S hS).map jE).base x ∈ (E : Set _) := by
        rw [← openObjectι_range B S hS W E]
        exact ⟨x, rfl⟩
      change k.base (((SmallEtale.toScheme B S hS).map jE).base x) ∈
        Set.range (pullback.diagonal qS).base at hxE
      simpa only [← Scheme.Hom.comp_apply] using hxE
    have hqeq : (SmallEtale.toScheme B S hS).map (jE ≫ a') =
        (SmallEtale.toScheme B S hS).map (jE ≫ b') := by
      have h := comp_fst_eq_comp_snd_of_range_subset_diagonal qS _ hsub
      simp only [k, Category.assoc, pullback.lift_fst, pullback.lift_snd] at h
      simpa only [Functor.map_comp] using h
    have hsite : jE ≫ a' = jE ≫ b' := (SmallEtale.toScheme B S hS).map_injective hqeq
    simpa [sa, sb, Functor.map_comp, Category.assoc] using
      congrArg (fun t => F.obj.map t.op s) hsite
  have hzero (c : W ⟶ X)
      (hc : ((SmallEtale.toScheme B S hS).map c).base ⁻¹' Set.range iS.base ⊆ A ∪ D) :
      F.obj.map jN.op (F.obj.map c.op s) = 0 := by
    apply section_restrict_zero_of_disjoint_support B S hS F W VN jN
    apply Set.disjoint_left.mpr
    intro x hx hsx
    have hxN : x ∈ (N : Set _) := (openObjectι_range B S hS W N).le hx
    exact hxN (hc (hs (supportSection_restrict_subset_preimage B S hS F X W c s hsx)))
  have hzeroA : F.obj.map jN.op sa = 0 := hzero a' fun _ hx => Or.inl hx
  have hzeroB : F.obj.map jN.op sb = 0 := hzero b' fun _ hx => Or.inr hx
  apply section_eq_of_restrict_eq_on_cover B S hS F V p hcov hetale sa sb
  intro b
  rcases b with ⟨b⟩
  cases b
  · simpa [p, V] using hrestrE
  · simpa [p, V] using hzeroA.trans hzeroB.symm

/-- The image of the selected branch over the closed image contains that closed image. -/
private theorem range_subset_range_selectedBranch_comp
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    (hφ : Etale ((SmallEtale.toScheme B S hS).map φ))
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)] :
    Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base ⊆
      Set.range ((SmallEtale.toScheme B S hS).map (openObjectι B S hS U'
        (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
          (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ)).base := by
  rintro _ ⟨z, rfl⟩
  have hO := (selectedBranchOpen_inter_preimage _ hφ _ i rfl).ge ⟨z, rfl⟩
  obtain ⟨y, hy⟩ := (openObjectι_range B S hS U' _).ge hO.1
  exact ⟨y, congrArg ((SmallEtale.toScheme B S hS).map φ).base hy⟩

private theorem cut_supportedSection_exists
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    (hφ : Etale ((SmallEtale.toScheme B S hS).map φ))
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (s : F.obj.obj (op U))
    (hs : supportSection B S hS F U s ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base) :
    ∃ s' : F.obj.obj (op U'),
      supportSection B S hS F U' s' ⊆ Set.range i.base ∧
      F.obj.map (openObjectι B S hS U'
        (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
          (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl)).op s' =
        F.obj.map (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ).op s := by
  classical
  let φs := (SmallEtale.toScheme B S hS).map φ
  let : Etale φs := hφ
  let g := i ≫ φs
  let O := selectedBranchOpen φs this g i rfl
  let R : Set ((SmallEtale.toScheme B S hS).obj U') := Set.range i.base
  have hR : IsClosed R := (IsClosedImmersion.isClosedEmbedding i).isClosed_range
  have hbranch : (O : Set ((SmallEtale.toScheme B S hS).obj U')) ∩
      (φs.base ⁻¹' Set.range g.base) = R :=
    selectedBranchOpen_inter_preimage φs this g i rfl
  have hsupport :
      supportSection B S hS F U' (F.obj.map φ.op s) ⊆
        φs.base ⁻¹' Set.range g.base :=
    (supportSection_restrict_subset_preimage B S hS F U U' φ s).trans
      (Set.preimage_mono hs)
  let jO := openObjectι B S hS U' O
  let jC := openObjectι B S hS U' ⟨Rᶜ, hR.isOpen_compl⟩
  obtain ⟨s', hsupp, hs'⟩ := exists_supportSection_subset_of_compatible_restrict B S hS F U'
    (openObject B S hS U' O) jO R hR
    (fun x hx => (openObjectι_range B S hS U' O).ge (hbranch.ge hx).1)
    (F.obj.map jO.op (F.obj.map φ.op s))
    (fun a b hab => by
      simpa [Functor.map_comp] using congrArg (fun t => F.obj.map t.op (F.obj.map φ.op s)) hab)
    (fun {Y} a b hab => by
      have hdisj : Disjoint (Set.range ((SmallEtale.toScheme B S hS).map (a ≫ jO)).base)
          (supportSection B S hS F U' (F.obj.map φ.op s)) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ hsx
        have hxC := comp_openObjectι_base_mem B S hS U' ⟨Rᶜ, hR.isOpen_compl⟩ b y
        rw [← hab] at hxC
        exact hxC (hbranch.le ⟨comp_openObjectι_base_mem B S hS U' O a y, hsupport hsx⟩)
      simpa [Functor.map_comp] using
        section_restrict_zero_of_disjoint_support B S hS F U' Y (a ≫ jO) (F.obj.map φ.op s) hdisj)
  refine ⟨s', hsupp, ?_⟩
  change F.obj.map jO.op s' = F.obj.map (jO ≫ φ).op s
  simpa [Functor.map_comp] using hs'

private theorem extend_supportedSection_exists
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    (hφ : Etale ((SmallEtale.toScheme B S hS).map φ))
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (s' : F.obj.obj (op U'))
    (hs' : supportSection B S hS F U' s' ⊆
      Set.range i.base) :
    ∃ s : F.obj.obj (op U),
      supportSection B S hS F U s ⊆
        Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base ∧
      F.obj.map (openObjectι B S hS U'
        (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
          (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ).op s =
        F.obj.map (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl)).op s' := by
  classical
  let φs := (SmallEtale.toScheme B S hS).map φ
  let g := i ≫ φs
  let O := selectedBranchOpen φs hφ g i rfl
  let R : Set ((SmallEtale.toScheme B S hS).obj U) := Set.range g.base
  have hR : IsClosed R := (IsClosedImmersion.isClosedEmbedding g).isClosed_range
  let jO := openObjectι B S hS U' O
  let jC := openObjectι B S hS U ⟨Rᶜ, hR.isOpen_compl⟩
  exact exists_supportSection_subset_of_compatible_restrict B S hS F U
    (openObject B S hS U' O) (jO ≫ φ) R hR
    (range_subset_range_selectedBranch_comp B S hS U U' φ Z' i hφ) (F.obj.map jO.op s')
    (fun a b hab => by
      simpa [Functor.map_comp] using
        supportedSection_restrict_eq_on_branch_overlap B S hS F U' U φ hφ Z' i O
          (selectedBranchOpen_inter_preimage φs hφ g i rfl) s' hs' _ a b hab)
    (fun {Y} a b hab => by
      have hdisj : Disjoint (Set.range ((SmallEtale.toScheme B S hS).map (a ≫ jO)).base)
          (supportSection B S hS F U' s') := by
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ hsx
        obtain ⟨z, hz⟩ := hs' hsx
        have hxC := comp_openObjectι_base_mem B S hS U ⟨Rᶜ, hR.isOpen_compl⟩ b y
        rw [← hab] at hxC
        exact hxC ⟨z, congrArg φs.base hz⟩
      simpa [Functor.map_comp] using
        section_restrict_zero_of_disjoint_support B S hS F U' Y (a ≫ jO) s' hdisj)

private theorem section_eq_of_supported_branch_restriction
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    (hφ : Etale ((SmallEtale.toScheme B S hS).map φ))
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (s t : F.obj.obj (op U))
    (hs : supportSection B S hS F U s ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base)
    (ht : supportSection B S hS F U t ⊆
      Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base)
    (hrestr : F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ).op s =
      F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl) ≫ φ).op t) :
    s = t := by
  exact eq_of_supportSection_subset_of_restrict_eq B S hS F U _ _ _
    (IsClosedImmersion.isClosedEmbedding (i ≫ (SmallEtale.toScheme B S hS).map φ)).isClosed_range
    (range_subset_range_selectedBranch_comp B S hS U U' φ Z' i hφ) s t hs ht hrestr

private theorem section_eq_of_supported_open_restriction
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U) (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    (hφ : Etale ((SmallEtale.toScheme B S hS).map φ))
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)]
    (s t : F.obj.obj (op U'))
    (hs : supportSection B S hS F U' s ⊆ Set.range i.base)
    (ht : supportSection B S hS F U' t ⊆ Set.range i.base)
    (hrestr : F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl)).op s =
      F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen ((SmallEtale.toScheme B S hS).map φ) hφ
            (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl)).op t) :
    s = t := by
  have hbranch := selectedBranchOpen_inter_preimage ((SmallEtale.toScheme B S hS).map φ) hφ
    (i ≫ (SmallEtale.toScheme B S hS).map φ) i rfl
  exact eq_of_supportSection_subset_of_restrict_eq B S hS F U' _ _ _
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range
    (fun x hx => (openObjectι_range B S hS U' _).ge (hbranch.ge hx).1) s t hs ht hrestr

/-- The canonical bijection between sections supported on corresponding closed
subschemes of two étale neighborhoods. -/
@[stacks 0F6F "canonical bijection"]
public noncomputable def supportedSectionsEquiv
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (φ : U' ⟶ U)
    (Z' : Scheme.{u})
    (i : Z' ⟶ (SmallEtale.toScheme B S hS).obj U')
    [IsClosedImmersion i]
    [IsClosedImmersion (i ≫ (SmallEtale.toScheme B S hS).map φ)] :
    {s : F.obj.obj (op U) //
        supportSection B S hS F U s ⊆
          Set.range (i ≫ (SmallEtale.toScheme B S hS).map φ).base} ≃
      {s' : F.obj.obj (op U') //
        supportSection B S hS F U' s' ⊆
          Set.range i.base} := by
  classical
  let φs := (SmallEtale.toScheme B S hS).map φ
  have hφ : Etale φs := etale_toScheme_map B S hS φ
  let Src := {s : F.obj.obj (op U) //
    supportSection B S hS F U s ⊆
      Set.range (i ≫ φs).base}
  let Tgt := {s' : F.obj.obj (op U') //
    supportSection B S hS F U' s' ⊆ Set.range i.base}
  let fwData (s : Src) :=
    cut_supportedSection_exists B S hS F U U' φ Z' i hφ s.val s.property
  let bwData (s' : Tgt) :=
    extend_supportedSection_exists B S hS F U U' φ Z' i hφ s'.val s'.property
  let fw : Src → Tgt := fun s => ⟨(Classical.choose (fwData s)),
    (Classical.choose_spec (fwData s)).1⟩
  let bw : Tgt → Src := fun s' => ⟨(Classical.choose (bwData s')),
    (Classical.choose_spec (bwData s')).1⟩
  refine ⟨fw, bw, ?_, ?_⟩
  · intro s
    apply Subtype.ext
    have hcut := Classical.choose_spec (fwData s)
    have hext := Classical.choose_spec (bwData (fw s))
    have hrestr : F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen φs hφ (i ≫ φs) i rfl) ≫ φ).op (bw (fw s)).val =
      F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen φs hφ (i ≫ φs) i rfl) ≫ φ).op s.val :=
      hext.2.trans hcut.2
    exact section_eq_of_supported_branch_restriction B S hS F U U' φ Z' i hφ
      (bw (fw s)).val s.val (bw (fw s)).property s.property hrestr
  · intro s'
    apply Subtype.ext
    have hext := Classical.choose_spec (bwData s')
    have hcut := Classical.choose_spec (fwData (bw s'))
    have hrestr : F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen φs hφ (i ≫ φs) i rfl)).op (fw (bw s')).val =
      F.obj.map
        (openObjectι B S hS U'
          (selectedBranchOpen φs hφ (i ≫ φs) i rfl)).op s'.val :=
      hcut.2.trans hext.2
    exact section_eq_of_supported_open_restriction B S hS F U U' φ Z' i hφ
      (fw (bw s')).val s'.val (fw (bw s')).property s'.property hrestr

end AlgebraicGeometry.SmallEtale

end
