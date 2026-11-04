module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PuncturedBaseCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.PolarGeometricInput
public import StacksFrontier.AlgebraicGeometry.FunctionField.SectionsIntersectionStalks

/-!
# Restriction of `H¹(X, 𝒪_X)` to the punctured part is injective

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` with punctured spectrum `U`, and a modification `f : X ⟶ Spec(A)` — let `X` be normal.
Then the restriction map `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` is injective. This is
[Stacks, Tag 0AXB]; the Nagata hypothesis of the source is not needed.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_d_eq_of_local_primitives`: a cocycle of an
  injective resolution of `𝒪_X` which has primitives on the members of an open cover containing
  `f⁻¹(U)` has a global primitive.
* `AlgebraicGeometry.VanishingSituation.firstCohomologyRestriction_injective`:
  [Stacks, Tag 0AXB].

## Implementation notes

The source proves the tag by a construction in the projective bundle of the extension attached
to a class in the kernel, followed by [Stacks, Tag 0AXA]. Here the negativity argument enters
instead through the polar lemma
`AlgebraicGeometry.forall_mem_stalkSubring_of_polar_of_isModification`, a statement about
rational functions. Cohomology is computed on an injective resolution
`0 ⟶ 𝒪_X ⟶ I⁰ ⟶ I¹ ⟶ ⋯`, so that `H¹(W, 𝒪_X)` is the first homology of `Γ(W, I^•)` and
restriction is restriction of cocycles (`InjectiveResolution.rightDerived_app_eq`). A cocycle `c`
whose class dies on `f⁻¹(U)` has a primitive there, and by locality of cohomology
([Stacks, Tag 01E3]) primitives `eⱼ` on an open cover. The differences of the primitives are
sections of `𝒪_X` because `𝒪_X` is the kernel of `I⁰ ⟶ I¹`; read at the generic point against the
primitive on `f⁻¹(U)`, they form a family of rational functions to which the polar lemma applies,
so each is regular on the corresponding member of the cover, and correcting the `eⱼ` by these
sections makes them agree on overlaps and glue to a global primitive.

No `@[stacks]` attribute is attached: Tag 0AXB is not proved here.

## References

* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PuncturedRestriction

/-- A class in the first homology of a cochain complex of abelian groups vanishes exactly when
a cocycle representing it is a coboundary. -/
theorem homologyπ_one_eq_zero_iff (K : CochainComplex AddCommGrpCat.{u} ℕ) (z : K.cycles 1) :
    K.homologyπ 1 z = 0 ↔ ∃ y : K.X 0, K.d 0 1 y = K.iCycles 1 z := by
  let S := ShortComplex.mk (K.toCycles 0 1) (K.homologyπ 1) (K.toCycles_comp_homologyπ 0 1)
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff S).mp
      (S.exact_of_g_is_cokernel (K.homologyIsCokernel 0 1 (by simp))) z hz
    exact ⟨y, (congrArg (fun k : K.X 0 ⟶ K.X 1 => k y) (K.toCycles_i 0 1)).symm.trans
      (congrArg (K.iCycles 1) hy)⟩
  · rintro ⟨y, hy⟩
    obtain rfl : K.toCycles 0 1 y = z :=
      (AddCommGrpCat.mono_iff_injective (K.iCycles 1)).mp inferInstance
        ((congrArg (fun k : K.X 0 ⟶ K.X 1 => k y) (K.toCycles_i 0 1)).trans hy)
    exact congrArg (fun k : K.X 0 ⟶ K.homology 1 => k y) (K.toCycles_comp_homologyπ 0 1)

variable {T : Type u} [TopologicalSpace T] {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]
  {M : SheafOfModules.{u} R} (I : InjectiveResolution M)

/-- The augmentation `M ⟶ I⁰` of an injective resolution. -/
def ι₀ : M ⟶ I.cocomplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 _).inv ≫ I.ι.f 0

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (SheafOfModules R)] in
/-- The augmentation is killed by the first differential. -/
theorem ι₀_comp_d : ι₀ I ≫ I.cocomplex.d 0 1 = 0 := by
  rw [ι₀, Category.assoc, InjectiveResolution.ι_f_zero_comp_complex_d, Limits.comp_zero]

/-- The augmentation is a kernel of the first differential. -/
def isLimitι₀ : IsLimit (KernelFork.ofι (ι₀ I) (ι₀_comp_d I)) :=
  IsLimit.ofIsoLimit I.isLimitKernelFork
    (Fork.ext (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M) (by
      change _ ≫ _ ≫ _ = I.ι.f 0
      exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).hom_inv_id_assoc
        (I.ι.f 0)))

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (SheafOfModules R)] in
/-- On sections over an open, `0 ⟶ Γ(V, M) ⟶ Γ(V, I⁰) ⟶ Γ(V, I¹)` is exact. -/
theorem exact_mono_secF_ι₀ (V : Opens T) :
    (ShortComplex.mk ((secF R V).map (ι₀ I)) ((secF R V).map (I.cocomplex.d 0 1))
      (by rw [← Functor.map_comp, ι₀_comp_d, Functor.map_zero])).Exact ∧
    Mono ((secF R V).map (ι₀ I)) :=
  (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2
    ⟨KernelFork.mapIsLimit _ (isLimitι₀ I) (secF R V)⟩

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (SheafOfModules R)] in
/-- The augmentation followed by the first differential vanishes on sections. -/
theorem secF_map_ι₀_d_apply (V : Opens T) (t : (secF R V).obj M) :
    (secF R V).map (I.cocomplex.d 0 1) ((secF R V).map (ι₀ I) t) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ι₀_comp_d, Functor.map_zero]
  rfl

omit [EnoughInjectives (SheafOfModules R)] in
variable (R) in
/-- If the restriction to `U` of the class of a cocycle of `Γ(V, I^•)` vanishes, then the
restriction of the cocycle is a coboundary on `U`. -/
theorem exists_d_eq_restrict {U V : Opens T} (h : U ≤ V) (z : (secCx R I V).cycles 1)
    (hz : HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (secRestrict R h) _).app I.cocomplex) 1
        ((secCx R I V).homologyπ 1 z) = 0) :
    ∃ e : (secF R U).obj (I.cocomplex.X 0),
      (secF R U).map (I.cocomplex.d 0 1) e =
        (secRestrict R h).app (I.cocomplex.X 1) ((secCx R I V).iCycles 1 z) := by
  set r := (NatTrans.mapHomologicalComplex (secRestrict R h) _).app I.cocomplex
  have hπ : HomologicalComplex.homologyMap r 1 ((secCx R I V).homologyπ 1 z) =
      (secCx R I U).homologyπ 1 (HomologicalComplex.cyclesMap r 1 z) :=
    congrArg (fun k => k z) (HomologicalComplex.homologyπ_naturality r 1)
  rw [hπ, homologyπ_one_eq_zero_iff] at hz
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy.trans (congrArg (fun k => k z) (HomologicalComplex.cyclesMap_i r 1))⟩

variable (R) in
/-- If a class of `H¹(W, M)` restricts to zero on `U`, then so does the class in the homology of
`Γ(W, I^•)` of any cocycle representing it. -/
theorem homologyMap_homologyπ_eq_zero {U W : Opens T} (h : U ≤ W) {ξ : Hgroup R W 1 M}
    (hξ : Hrestrict R h 1 M ξ = 0) (z : (secCx R I W).cycles 1)
    (hz : (secCx R I W).homologyπ 1 z = (I.isoRightDerivedObj (secF R W) 1).hom ξ) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (secRestrict R h) _).app I.cocomplex) 1
        ((secCx R I W).homologyπ 1 z) = 0 := by
  have hkey : Hrestrict R h 1 M = (I.isoRightDerivedObj (secF R W) 1).hom ≫
      (HomologicalComplex.homologyFunctor _ _ 1).map
        ((NatTrans.mapHomologicalComplex (secRestrict R h) _).app I.cocomplex) ≫
      (I.isoRightDerivedObj (secF R U) 1).inv :=
    InjectiveResolution.rightDerived_app_eq (secRestrict R h) I 1
  rw [hkey] at hξ
  have h1 := congrArg (I.isoRightDerivedObj (secF R U) 1).hom hξ
  rw [map_zero, ← ConcreteCategory.comp_apply, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ConcreteCategory.comp_apply] at h1
  rwa [hz]

end AlgebraicGeometry.PuncturedRestriction

namespace AlgebraicGeometry.PuncturedRestriction

variable (V : VanishingSituation.{u})

/-- A section of the structure sheaf, read in the module-valued model, as a section of `𝒪_X`. -/
def toΓ {U : V.X.Opens}
    (s : (secF V.structureRingSheaf U).obj (SheafOfModules.unit V.structureRingSheaf)) :
    Γ(V.X, U) := s

/-- `toΓ` commutes with restriction. -/
theorem toΓ_res {U U' : V.X.Opens} (h : U' ≤ U)
    (s : (secF V.structureRingSheaf U).obj (SheafOfModules.unit V.structureRingSheaf)) :
    toΓ V ((secRestrict V.structureRingSheaf h).app _ s) =
      V.X.presheaf.map (homOfLE h).op (toΓ V s) := rfl

/-- `toΓ` is additive. -/
theorem toΓ_sub {U : V.X.Opens}
    (s t : (secF V.structureRingSheaf U).obj (SheafOfModules.unit V.structureRingSheaf)) :
    toΓ V (s - t) = toΓ V s - toΓ V t := rfl

end AlgebraicGeometry.PuncturedRestriction

namespace AlgebraicGeometry.PuncturedRestriction

section Polar

variable {T : Type u} [TopologicalSpace T] (R : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- Restrictions of sections compose. -/
theorem secRestrict_app_comp {U V W : Opens T} (h₁ : U ≤ V) (h₂ : V ≤ W) (M : SheafOfModules R)
    (s : (secF R W).obj M) :
    (secRestrict R h₁).app M ((secRestrict R h₂).app M s) =
      (secRestrict R (h₁.trans h₂)).app M s := by
  change ((SheafOfModules.toSheaf R).obj M).obj.map (homOfLE h₁).op
      (((SheafOfModules.toSheaf R).obj M).obj.map (homOfLE h₂).op s) =
    ((SheafOfModules.toSheaf R).obj M).obj.map (homOfLE (h₁.trans h₂)).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of sections commutes with morphisms of sheaves of modules. -/
theorem secRestrict_app_map {U V : Opens T} (h : U ≤ V) {M N : SheafOfModules R} (φ : M ⟶ N)
    (s : (secF R V).obj M) :
    (secRestrict R h).app N ((secF R V).map φ s) =
      (secF R U).map φ ((secRestrict R h).app M s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (secRestrict R h).naturality φ]

end Polar

section Primitives

variable {T : Type u} [TopologicalSpace T] {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]
  {M : SheafOfModules.{u} R} (I : InjectiveResolution M)

omit [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (SheafOfModules R)] in
/-- Two primitives of the same cocycle of `Γ(W, I^•)` differ on their overlap by a section of
`M`. -/
theorem exists_secF_map_ι₀_eq_sub {U₁ U₂ W : Opens T} (h₁ : U₁ ≤ W) (h₂ : U₂ ≤ W)
    (c : (secF R W).obj (I.cocomplex.X 1))
    (e₁ : (secF R U₁).obj (I.cocomplex.X 0)) (e₂ : (secF R U₂).obj (I.cocomplex.X 0))
    (he₁ : (secF R U₁).map (I.cocomplex.d 0 1) e₁ = (secRestrict R h₁).app _ c)
    (he₂ : (secF R U₂).map (I.cocomplex.d 0 1) e₂ = (secRestrict R h₂).app _ c) :
    ∃ t : (secF R (U₁ ⊓ U₂)).obj M,
      (secF R _).map (ι₀ I) t = (secRestrict R inf_le_left).app _ e₁ -
        (secRestrict R inf_le_right).app _ e₂ := by
  refine (ShortComplex.ab_exact_iff _).mp (exact_mono_secF_ι₀ I (U₁ ⊓ U₂)).1 _ ?_
  change (secF R _).map (I.cocomplex.d 0 1) (_ - _) = 0
  rw [map_sub, ← secRestrict_app_map, ← secRestrict_app_map, he₁, he₂, secRestrict_app_comp,
    secRestrict_app_comp, sub_self]

end Primitives

end AlgebraicGeometry.PuncturedRestriction

namespace AlgebraicGeometry.PuncturedRestriction

section Gluing

variable (V : VanishingSituation.{u})

local notation "𝒪" => VanishingSituation.structureRingSheaf V

/-- Sections of an abelian sheaf over an open with no points agree. -/
theorem eq_of_isEmpty {G : Sheaf (Opens.grothendieckTopology V.X) AddCommGrpCat.{u}}
    {U : V.X.Opens} (hU : ∀ x : V.X, x ∉ U) (a b : ToType (G.obj.obj (op U))) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' (F := (⟨G.obj, G.property⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} V.X.carrier)) (fun i : PEmpty.{u + 1} => PEmpty.elim i) U
    (fun i => PEmpty.elim i) (fun x hx => (hU x hx).elim) a b (fun i => PEmpty.elim i)

end Gluing

end AlgebraicGeometry.PuncturedRestriction

namespace AlgebraicGeometry.PuncturedRestriction

section Lifts

variable (V : VanishingSituation.{u})

local notation "𝒪" => VanishingSituation.structureRingSheaf V

/-- A point lies over the punctured spectrum exactly when it does not lie over the closed point. -/
theorem mem_preimagePuncturedSpectrum_iff (x : V.X) :
    x ∈ V.preimagePuncturedSpectrum ↔ V.f x ≠ V.closedPoint := Iff.rfl

/-- Every open of `X` containing a point contains the generic point. -/
theorem genericPoint_mem_of_mem [IsIntegral V.X] {W : V.X.Opens} {x : V.X} (hx : x ∈ W) :
    genericPoint V.X ∈ W :=
  ((genericPoint_spec V.X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩

/-- The generic point lies in the intersection of two opens that each contain some point. -/
private theorem genericPoint_mem_inf_of_mem [IsIntegral V.X] {W W' : V.X.Opens} {x y : V.X}
    (hx : x ∈ W) (hy : y ∈ W') : genericPoint V.X ∈ W ⊓ W' :=
  Opens.mem_inf.mpr ⟨genericPoint_mem_of_mem V hx, genericPoint_mem_of_mem V hy⟩

/-- The generic point of `X` lies over the punctured spectrum. -/
theorem genericPoint_mem_preimagePuncturedSpectrum [IsIntegral V.X] :
    genericPoint V.X ∈ V.preimagePuncturedSpectrum :=
  apply_genericPoint_ne_closedPoint V.dimension_two V.f V.modification

/-- Germs of sections of `𝒪_X` commute with restriction. -/
theorem germ_toΓ_secRestrict {W W' : V.X.Opens} (hle : W' ≤ W) {x : V.X} (hx : x ∈ W')
    (t : (secF 𝒪 W).obj (SheafOfModules.unit 𝒪)) :
    V.X.presheaf.germ W' x hx (toΓ V ((secRestrict 𝒪 hle).app _ t)) =
      V.X.presheaf.germ W x (hle hx) (toΓ V t) :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE hle) x hx _

/-- Germs of sections of `𝒪_X` are additive. -/
theorem germ_toΓ_sub {W : V.X.Opens} {x : V.X} (hx : x ∈ W)
    (t t' : (secF 𝒪 W).obj (SheafOfModules.unit 𝒪)) :
    V.X.presheaf.germ W x hx (toΓ V (t - t')) =
      V.X.presheaf.germ W x hx (toΓ V t) - V.X.presheaf.germ W x hx (toΓ V t') := by
  rw [toΓ_sub, map_sub]

/-- The rational function of a section of `𝒪_X` over `W` is regular at every point of `W`. -/
theorem germ_toΓ_mem_stalkSubring [IsIntegral V.X] {W : V.X.Opens} (hW : genericPoint V.X ∈ W)
    {y : V.X} (hy : y ∈ W) (t : (secF 𝒪 W).obj (SheafOfModules.unit 𝒪)) :
    (V.X.presheaf.germ W _ hW (toΓ V t) : V.X.functionField) ∈ stalkSubring y := by
  refine ⟨V.X.presheaf.germ W y hy (toΓ V t), ?_⟩
  change V.X.presheaf.stalkSpecializes _ (V.X.presheaf.germ W y hy (toΓ V t)) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

/-- A section of `𝒪_X` is determined by its rational function. -/
theorem germ_toΓ_injective [IsIntegral V.X] {W : V.X.Opens} (hW : genericPoint V.X ∈ W)
    {t t' : (secF 𝒪 W).obj (SheafOfModules.unit 𝒪)}
    (h : V.X.presheaf.germ W _ hW (toΓ V t) = V.X.presheaf.germ W _ hW (toΓ V t')) : t = t' :=
  germ_injective_of_isIntegral (X := V.X) _ hW h

/-- The cocycle identity on triple intersections with `U j₀`, read on germs. -/
theorem germ_sub_eq_of_cocycle {J : Type u} {U : J → V.X.Opens} {j₀ : J}
    {s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (SheafOfModules.unit 𝒪)}
    (hkey : ∀ a b, (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U j₀)).app _ (s a j₀) -
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U b ⊓ U j₀)).app _ (s b j₀) =
      (secRestrict 𝒪 (inf_le_left : U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U b)).app _ (s a b))
    {x : V.X} (a b : J) (ha : x ∈ U a ⊓ U j₀) (hb : x ∈ U b ⊓ U j₀) (hab : x ∈ U a ⊓ U b) :
    V.X.presheaf.germ _ x ha (toΓ V (s a j₀)) - V.X.presheaf.germ _ x hb (toΓ V (s b j₀)) =
      V.X.presheaf.germ _ x hab (toΓ V (s a b)) := by
  have h3 : x ∈ U a ⊓ U b ⊓ U j₀ := Opens.mem_inf.mpr ⟨hab, (Opens.mem_inf.mp ha).2⟩
  have := congrArg (V.X.presheaf.germ _ x h3) (congrArg (toΓ V) (hkey a b))
  rwa [germ_toΓ_sub, germ_toΓ_secRestrict, germ_toΓ_secRestrict, germ_toΓ_secRestrict] at this

/-- **The polar step.** Let `s` be a family of sections of `𝒪_X` on the overlaps of an open cover
containing `U j₀ = f⁻¹(U)`, satisfying the cocycle identity against `U j₀`. Then on each member
`U a` of the cover there is a section of `𝒪_X` with the rational function of `s a j₀`. -/
theorem exists_germ_eq_of_cocycle [IsNormal V.X] [IsIntegral V.X] {J : Type u}
    (U : J → V.X.Opens) (hU : ∀ x : V.X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : U j₀ = V.preimagePuncturedSpectrum)
    (s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (SheafOfModules.unit 𝒪))
    (hkey : ∀ a b, (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U j₀)).app _ (s a j₀) -
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U b ⊓ U j₀)).app _ (s b j₀) =
      (secRestrict 𝒪 (inf_le_left : U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U b)).app _ (s a b))
    (a : J) :
    ∃ t : (secF 𝒪 (U a)).obj (SheafOfModules.unit 𝒪),
      ∀ (h₁ : genericPoint V.X ∈ U a) (h₂ : genericPoint V.X ∈ U a ⊓ U j₀),
        V.X.presheaf.germ _ _ h₁ (toΓ V t) = V.X.presheaf.germ _ _ h₂ (toΓ V (s a j₀)) := by
  choose j hj using hU
  set η := genericPoint V.X
  have hηW : η ∈ U j₀ := hj₀ ▸ genericPoint_mem_preimagePuncturedSpectrum V
  have hηj : ∀ x, η ∈ U (j x) ⊓ U j₀ := fun x => genericPoint_mem_inf_of_mem V (hj x) hηW
  let h : V.X → V.X.functionField := fun x => V.X.presheaf.germ _ η (hηj x) (toΓ V (s (j x) j₀))
  have hA : ∀ y : V.X, Order.coheight y = 1 → V.f y ≠ IsLocalRing.closedPoint V.A →
      h y ∈ stalkSubring y := fun y _ hy =>
    germ_toΓ_mem_stalkSubring V _ (Opens.mem_inf.mpr ⟨hj y, hj₀ ▸ hy⟩) _
  have hB : ∀ x : V.X, ∃ W : V.X.Opens, x ∈ W ∧ ∀ y ∈ W, h x - h y ∈ stalkSubring y := by
    refine fun x => ⟨U (j x), hj x, fun y hy => ?_⟩
    have hab : η ∈ U (j x) ⊓ U (j y) := genericPoint_mem_inf_of_mem V (hj x) (hj y)
    rw [show h x - h y = _ from germ_sub_eq_of_cocycle V hkey _ _ (hηj x) (hηj y) hab]
    exact germ_toΓ_mem_stalkSubring V hab (Opens.mem_inf.mpr ⟨hy, hj y⟩) _
  have hpolar := forall_mem_stalkSubring_of_polar_of_isModification V.dimension_two V.f
    V.modification h hA hB
  by_cases hne : η ∈ U a
  · have : Nonempty (U a) := ⟨⟨η, hne⟩⟩
    have hne' : η ∈ U a ⊓ U j₀ := Opens.mem_inf.mpr ⟨hne, hηW⟩
    obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_forall_mem_range V.X (U a)
      (V.X.presheaf.germ _ η hne' (toΓ V (s a j₀)) : V.X.functionField) (fun x => by
        have hx' : η ∈ U (j x.1) ⊓ U a := genericPoint_mem_inf_of_mem V (hj x.1) hne
        have e₁ := germ_sub_eq_of_cocycle V hkey (j x.1) a (hηj x.1) hne' hx'
        have hx : V.X.presheaf.germ _ η hne' (toΓ V (s a j₀)) =
            h x.1 - V.X.presheaf.germ _ η hx' (toΓ V (s (j x.1) a)) := by
          rw [← e₁]
          abel
        rw [hx]
        exact sub_mem (hpolar x.1)
          (germ_toΓ_mem_stalkSubring V _ (Opens.mem_inf.mpr ⟨hj x.1, x.2⟩) _))
    exact ⟨t, fun _ _ => ht⟩
  · exact ⟨0, fun h₁ => absurd h₁ hne⟩

/-- A family of sections of `𝒪_X` on the overlaps of an open cover containing `U j₀ = f⁻¹(U)`,
satisfying the cocycle identity against `U j₀`, is a coboundary. -/
theorem exists_eq_sub_of_cocycle_of_polar [IsNormal V.X] [IsIntegral V.X] {J : Type u}
    (U : J → V.X.Opens) (hU : ∀ x : V.X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : U j₀ = V.preimagePuncturedSpectrum)
    (s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (SheafOfModules.unit 𝒪))
    (hkey : ∀ a b, (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U j₀)).app _ (s a j₀) -
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U b ⊓ U j₀)).app _ (s b j₀) =
      (secRestrict 𝒪 (inf_le_left : U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U b)).app _ (s a b)) :
    ∃ t : ∀ a, (secF 𝒪 (U a)).obj (SheafOfModules.unit 𝒪), ∀ a b,
      s a b = (secRestrict 𝒪 inf_le_left).app _ (t a) -
        (secRestrict 𝒪 (inf_le_right : U a ⊓ U b ≤ U b)).app _ (t b) := by
  choose t ht using exists_germ_eq_of_cocycle V U hU j₀ hj₀ s hkey
  refine ⟨t, fun a b => ?_⟩
  have hηW : genericPoint V.X ∈ U j₀ := hj₀ ▸ genericPoint_mem_preimagePuncturedSpectrum V
  by_cases hab : genericPoint V.X ∈ U a ⊓ U b
  · obtain ⟨ha, hb⟩ := Opens.mem_inf.mp hab
    have ha' : genericPoint V.X ∈ U a ⊓ U j₀ := genericPoint_mem_inf_of_mem V ha hηW
    have hb' : genericPoint V.X ∈ U b ⊓ U j₀ := genericPoint_mem_inf_of_mem V hb hηW
    apply germ_toΓ_injective V hab
    rw [germ_toΓ_sub, germ_toΓ_secRestrict, germ_toΓ_secRestrict, ht a ha ha', ht b hb hb',
      germ_sub_eq_of_cocycle V hkey a b ha' hb' hab]
  · exact eq_of_isEmpty V (G := (SheafOfModules.toSheaf 𝒪).obj (SheafOfModules.unit 𝒪))
      (fun x hx => hab (genericPoint_mem_inf_of_mem V (Opens.mem_inf.mp hx).1
        (Opens.mem_inf.mp hx).2)) _ _

/-- **Local primitives of a cocycle that glue.** Let `I` be an injective resolution of `𝒪_X`, let
`c ∈ Γ(X, I¹)` and let `eⱼ ∈ Γ(Uⱼ, I⁰)` be primitives of `c` on the members of an open cover, one
of which is `f⁻¹(U)`. Then `c` has a primitive on `X`. The differences of the `eⱼ` are sections of
`𝒪_X`; read as rational functions against the member `f⁻¹(U)`, they satisfy the hypotheses of the
polar lemma `AlgebraicGeometry.forall_mem_stalkSubring_of_polar_of_isModification`, which makes
them regular, and correcting each `eⱼ` by the corresponding section of `𝒪_X` makes them glue. -/
theorem exists_d_eq_of_local_primitives [IsNormal V.X] [IsIntegral V.X]
    (I : InjectiveResolution (SheafOfModules.unit 𝒪))
    {J : Type u} (U : J → V.X.Opens) (hU : ∀ x : V.X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : U j₀ = V.preimagePuncturedSpectrum)
    (c : (secF 𝒪 ⊤).obj (I.cocomplex.X 1))
    (e : ∀ j, (secF 𝒪 (U j)).obj (I.cocomplex.X 0))
    (he : ∀ j, (secF 𝒪 (U j)).map (I.cocomplex.d 0 1) (e j) =
      (secRestrict 𝒪 (le_top : U j ≤ ⊤)).app _ c) :
    ∃ ε : (secF 𝒪 ⊤).obj (I.cocomplex.X 0), (secF 𝒪 ⊤).map (I.cocomplex.d 0 1) ε = c := by
  -- Step 1: the differences of the primitives are sections of `𝒪_X`.
  choose s hs using fun a b =>
    exists_secF_map_ι₀_eq_sub I le_top le_top c (e a) (e b) (he a) (he b)
  -- Step 2: the cocycle identity on triple intersections with `U j₀`.
  have hkey : ∀ a b, (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U j₀)).app _ (s a j₀) -
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U b ⊓ U j₀)).app _ (s b j₀) =
      (secRestrict 𝒪 (inf_le_left : U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U b)).app _ (s a b) := by
    intro a b
    apply (AddCommGrpCat.mono_iff_injective _).mp (exact_mono_secF_ι₀ I _).2
    simp only [map_sub, ← secRestrict_app_map, hs, secRestrict_app_comp]
    abel
  -- Step 3: the polar lemma makes the differences coboundaries.
  obtain ⟨t, ht⟩ := exists_eq_sub_of_cocycle_of_polar V U hU j₀ hj₀ s hkey
  -- Step 4: the corrected primitives are compatible.
  let ε' : ∀ a, (secF 𝒪 (U a)).obj (I.cocomplex.X 0) :=
    fun a => e a - (secF 𝒪 (U a)).map (ι₀ I) (t a)
  have hcompat : ∀ a b, (secRestrict 𝒪 inf_le_left).app _ (ε' a) =
      (secRestrict 𝒪 (inf_le_right : U a ⊓ U b ≤ U b)).app _ (ε' b) := by
    intro a b
    have h₁ := congrArg ((secF 𝒪 _).map (ι₀ I)) (ht a b)
    rw [hs, map_sub, ← secRestrict_app_map, ← secRestrict_app_map] at h₁
    simp only [ε', map_sub]
    rwa [sub_eq_sub_iff_sub_eq_sub]
  -- Step 5: glue, and check the differential locally.
  let G₀ : TopCat.Sheaf AddCommGrpCat.{u} V.X.carrier :=
    ⟨((SheafOfModules.toSheaf 𝒪).obj (I.cocomplex.X 0)).obj,
      ((SheafOfModules.toSheaf 𝒪).obj (I.cocomplex.X 0)).property⟩
  let G₁ : TopCat.Sheaf AddCommGrpCat.{u} V.X.carrier :=
    ⟨((SheafOfModules.toSheaf 𝒪).obj (I.cocomplex.X 1)).obj,
      ((SheafOfModules.toSheaf 𝒪).obj (I.cocomplex.X 1)).property⟩
  have hcov : (⊤ : V.X.Opens) ≤ iSup U := fun x _ => Opens.mem_iSup.mpr (hU x)
  obtain ⟨ε, hε, -⟩ := TopCat.Sheaf.existsUnique_gluing' G₀ U ⊤ (fun a => homOfLE le_top) hcov
    ε' hcompat
  refine ⟨ε, TopCat.Sheaf.eq_of_locally_eq' G₁ U ⊤ (fun a => homOfLE le_top) hcov _ _
    (fun a => ?_)⟩
  change (secRestrict 𝒪 le_top).app _ ((secF 𝒪 ⊤).map (I.cocomplex.d 0 1) ε) =
    (secRestrict 𝒪 le_top).app _ c
  rw [secRestrict_app_map, show (secRestrict 𝒪 le_top).app _ ε = ε' a from hε a]
  simpa only [ε', map_sub, secF_map_ι₀_d_apply I, sub_zero] using he a

end Lifts

end AlgebraicGeometry.PuncturedRestriction

namespace AlgebraicGeometry.VanishingSituation

open PuncturedRestriction

variable (V : VanishingSituation.{u})

/-- **[Stacks, Tag 0AXB].** In Situation 0AX8 with `X` normal, the restriction map
`H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` on the first cohomology of the structure sheaf is injective.

The source assumes `A` Nagata as well; the argument below does not use it. A class in the
kernel is represented, through an injective resolution `I` of `𝒪_X`, by a cocycle `c ∈ Γ(X, I¹)`
which has primitives on `f⁻¹(U)` and on the members of an open cover of `X` (locality of
cohomology, [Stacks, Tag 01E3]); `exists_d_eq_of_local_primitives` glues them, using the polar
lemma in place of the projective-bundle construction of the source's proof. -/
theorem firstCohomologyRestriction_injective [IsNormal V.X] :
    Function.Injective V.firstCohomologyRestriction := by
  have : IsIntegral V.X := V.modification.source_isIntegral
  set 𝒪 := V.structureRingSheaf
  set O := SheafOfModules.unit 𝒪
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
  set I : InjectiveResolution O := InjectiveResolution.of O
  set ξ' := (I.isoRightDerivedObj (secF 𝒪 ⊤) 1).hom ξ with hξ'
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective
    ((secCx 𝒪 I ⊤).homologyπ 1)).mp inferInstance ξ'
  obtain ⟨eW, heW⟩ := exists_d_eq_restrict 𝒪 I le_top z
    (homologyMap_homologyπ_eq_zero 𝒪 I (le_top : V.preimagePuncturedSpectrum ≤ ⊤) (ξ := ξ) hξ
      z hz)
  -- primitives on a cover
  obtain ⟨J, cover, hle, hsup, hzero⟩ :=
    exists_cover_homologyMap_eq_zero 𝒪 O ⊤ 1 one_pos I ξ'
  choose ei hei using fun i => exists_d_eq_restrict 𝒪 I (hle i) z (by rw [hz]; exact hzero i)
  let U : Option J → V.X.Opens := fun o => o.elim V.preimagePuncturedSpectrum cover
  have hU : ∀ x : V.X, ∃ o, x ∈ U o := by
    intro x
    have hx : x ∈ (⨆ i, cover i) := by rw [hsup]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨some i, hi⟩
  let e : ∀ o, (secF 𝒪 (U o)).obj (I.cocomplex.X 0) := fun
    | none => eW
    | some i => ei i
  have he : ∀ o, (secF 𝒪 (U o)).map (I.cocomplex.d 0 1) (e o) =
      (secRestrict 𝒪 (le_top : U o ≤ ⊤)).app _ ((secCx 𝒪 I ⊤).iCycles 1 z) := fun
    | none => heW
    | some i => hei i
  obtain ⟨ε, hε⟩ := exists_d_eq_of_local_primitives V I U hU none rfl _ e he
  have hξ'0 : ξ' = 0 := hz.symm.trans ((homologyπ_one_eq_zero_iff _ z).mpr ⟨ε, hε⟩)
  have := congrArg (I.isoRightDerivedObj (secF 𝒪 ⊤) 1).inv hξ'0
  rwa [hξ', ← ConcreteCategory.comp_apply, Iso.hom_inv_id, map_zero] at this

end AlgebraicGeometry.VanishingSituation

end
