module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The inverse image of a sheaf of graded sets along a morphism of topoi

A sheaf of graded sets on a site `(C, J)` is a sheaf of sets `S` together with a degree morphism
`S ⟶ ℤ` into the constant sheaf of integers. Let `f : Sh(C₁, J₁) ⟶ Sh(C, J)` be a morphism of
topoi. Its inverse image `f⁻¹` is a left adjoint and is left exact, so it carries the constant
sheaf of integers to the constant sheaf of integers: the constant sheaf of integers is the
coproduct of `ℤ` copies of the terminal sheaf, a left adjoint preserves that coproduct and a
left exact functor preserves the terminal object. Transporting the degree morphism along that
identification makes `f⁻¹S` a sheaf of graded sets on `(C₁, J₁)`, and the same two facts
identify the inverse image of the sheaf of degree-`i` local sections of `S` with the sheaf of
degree-`i` local sections of `f⁻¹S`: **the grading survives, degree by degree.**

This is the sheaf-of-sets half of the third paragraph of the source's proof of Tag 0FSG, which
identifies the pullback `f^*A[S]` of a free differential graded module with the free module
`A'[f^{-1}S]` on the inverse image of the sheaf of graded sets. The module half is
`SheafOfModules.freeDGModule_baseChange_of_free` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleBaseChange.lean`, and what remains
between the two is recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleFlat.lean`.

Nothing here assumes a functor between the two underlying categories, let alone a continuous
one, and nothing relates the universes of the two sites or the two universes of coefficients: a
morphism of topoi carries `f⁻¹` as data, so no left Kan extension has to be formed and no
smallness hypothesis arises.

## Main definitions

* `Stacks.SheafOfGradedSets.inverseImage`: **the inverse image of a sheaf of graded sets along a
  morphism of topoi.**
* `Stacks.eqFiber` and `Stacks.eqFiberSheaf`: the sheaf of local sections on which two morphisms
  of sheaves of sets agree, together with `Stacks.eqFiberSheafIso` identifying it with their
  equalizer, `Stacks.eqFiberι` its inclusion into the source sheaf (a monomorphism), and
  `Stacks.eqFiberSheafCongrIso` the comparison of two such fibres.
* `Stacks.eqFiberSheafPreservesIso`: **a functor preserving the relevant equalizer carries an
  equation fibre to the equation fibre of the images**, with
  `eqFiberSheafPreservesIso_hom_comp_ι` identifying the comparison by its compatibility with the
  two inclusions. This is what both `f⁻¹` and `f_*` apply through.
* `Stacks.degreeFiber` and `Stacks.degreeFiberSheaf`: the sheaf of degree-`i` local sections of a
  sheaf of graded sets, as the equation fibre of the degree morphism against the constant `i`.
* `Stacks.constantDegreeMap` and `Stacks.terminalDegree`: the morphism carrying every local
  section to the constant degree `i`, and its factorisation through the terminal sheaf.

## Main results

* `Stacks.inverseImageConstantIntegerIso`: **`f⁻¹` of the constant sheaf of integers is the
  constant sheaf of integers.**
* `Stacks.inverseImageDegreeFiberIso`: **the grading survives the inverse image, degree by
  degree** — `f⁻¹` of the sheaf of degree-`i` local sections of `S` is the sheaf of degree-`i`
  local sections of `f⁻¹S` — and `inverseImageDegreeFiberIso_hom_comp_ι`, which pins it down by
  its compatibility with the two inclusions. It is now an instance of
  `Stacks.eqFiberSheafPreservesIso` rather than a second copy of that argument.
* `Stacks.constantIntegerSheafIso`: the constant sheaf of integers is the coproduct of `ℤ` copies
  of the terminal sheaf, which is what makes the two statements above provable from left
  exactness and the adjunction alone.

## Implementation notes

`HasSheafify J (Type m)` is carried rather than the weaker `HasWeakSheafify J (Type m)` that
`Stacks.SheafOfGradedSets` itself needs. It is used for one thing: the constant sheaf functor is
left exact, which is `Stacks.preservesFiniteLimits_constantSheaf`, and that is what identifies
the constant sheaf on a singleton with the terminal sheaf. Mathlib supplies
`HasSheafify J (Type (max u v))` automatically for a site `C : Type u` with
`[Category.{v} C]`, so the hypothesis is automatic at the universe where the source's sites live
and is an instance hypothesis, not a mathematical one, elsewhere. No hypothesis is placed on any
functor of the two sites, there being none in the statements, and none relates `m` to `m₁`.

The degree-`i` fibre is defined as the subtype presheaf of local sections of degree `i` and only
then compared with the equalizer of the degree morphism and the constant `i`, in
`Stacks.degreeFiberSheafIso`. Both spellings are wanted: the subtype is what a consumer reading
off a generator of degree `i` needs, and the equalizer is what left exactness of `f⁻¹` applies
to. The sheaf condition for the subtype presheaf is proved by exhibiting it as a limit of the
parallel pair in presheaves, through `CategoryTheory.Sheaf.isSheaf_of_isLimit`.

Both constructions are the one construction `Stacks.eqFiber`, the subtype presheaf cut out by an
equation between two morphisms of sheaves of sets: `Stacks.degreeFiber` is it at the degree
morphism and the constant `i`, and `SheafOfModules.DifferentialGradedModule.closedSection` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedClosedSections.lean` is it at the
differential and zero. The generic form carries no `HasSheafify` hypothesis — the constant sheaf
enters only through `Stacks.constantDegreeMap` — which is why the sheaf of closed sections of a
right differential graded module needs none.

`Stacks.preservesFiniteLimits_constantSheaf` is stated as a theorem rather than registered as an
instance: its proof goes through `CategoryTheory.Limits.comp_preservesFiniteLimits`, which is not
an instance, so instance search does not find it even though both factors of
`constantSheaf = Functor.const ⋙ presheafToSheaf` have the property. The two facts about `f⁻¹`
are registered as instances, being projections of the fields of `MorphismOfTopoi`.

## References

* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe m₁ v₁ u₁ m v u

namespace Stacks

/-- The coproduct of `ℤ` copies of a singleton is `ℤ`. -/
noncomputable def integerCoproductIso : (∐ fun _ : ℤ => PUnit.{m + 1}) ≅ ULift.{m} ℤ :=
  Types.coproductIso (fun _ : ℤ => PUnit.{m + 1}) ≪≫
    Equiv.toIso
      { toFun := fun x => ⟨x.1⟩
        invFun := fun x => ⟨x.down, PUnit.unit⟩
        left_inv := by rintro ⟨i, ⟨⟩⟩; rfl
        right_inv := by intro x; cases x; rfl }

/-- The coproduct inclusion of the summand `i` into `ℤ` copies of a singleton is the constant
map `i`. -/
theorem integerCoproductIso_ι (i : ℤ) :
    Sigma.ι (fun _ : ℤ => PUnit.{m + 1}) i ≫ integerCoproductIso.hom =
      ↾fun _ => (⟨i⟩ : ULift.{m} ℤ) := by
  unfold integerCoproductIso
  rw [Iso.trans_hom, ← Category.assoc, Types.coproductIso_ι_comp_hom]
  rfl

/-- The inverse image of a morphism of topoi is left exact: that is one of its fields. -/
instance preservesFiniteLimits_toposInverseImage {E : Type*} [Category* E] {F : Type*}
    [Category* F] (f : MorphismOfTopoi E F) : PreservesFiniteLimits f.inverseImage :=
  f.preservesFiniteLimits

/-- The inverse image of a morphism of topoi is a left adjoint: its adjunction is one of its
fields. -/
instance isLeftAdjoint_toposInverseImage {E : Type*} [Category* E] {F : Type*} [Category* F]
    (f : MorphismOfTopoi E F) : f.inverseImage.IsLeftAdjoint :=
  ⟨f.pushforward, ⟨f.adj⟩⟩

/-- A functor preserving a coproduct carries its inclusions to the inclusions. -/
theorem map_ι_preservesCoproductIso_hom {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {I : Type*} (K : I → D) [HasCoproduct K] [HasCoproduct fun i => F.obj (K i)]
    [PreservesColimit (Discrete.functor K) F] (i : I) :
    F.map (Sigma.ι K i) ≫ (PreservesCoproduct.iso F K).hom =
      Sigma.ι (fun i => F.obj (K i)) i := by
  apply (cancel_mono (PreservesCoproduct.iso F K).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison]

/-! ### The constant sheaf of integers -/

section ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J (Type m)]

/-- The constant sheaf functor is left exact, being the constant presheaf functor followed by
sheafification. -/
theorem preservesFiniteLimits_constantSheaf :
    PreservesFiniteLimits (constantSheaf J (Type m)) := by
  unfold constantSheaf
  exact comp_preservesFiniteLimits _ _

/-- The constant sheaf functor preserves coproducts, being a left adjoint. -/
theorem preservesColimit_constantSheaf {ι : Type*} (K : ι → Type m) :
    PreservesColimit (Discrete.functor K) (constantSheaf J (Type m)) := by
  unfold constantSheaf
  infer_instance

/-- The constant sheaf on a singleton is a terminal sheaf. -/
noncomputable def constantUnitSheafIso :
    (constantSheaf J (Type m)).obj PUnit.{m + 1} ≅ ⊤_ (Sheaf J (Type m)) :=
  haveI : PreservesFiniteLimits (constantSheaf J (Type m)) :=
    preservesFiniteLimits_constantSheaf J
  (Types.isTerminalPUnit.isTerminalObj (constantSheaf J (Type m)) PUnit.{m + 1}).uniqueUpToIso
    terminalIsTerminal

/-- **The constant sheaf of integers is the coproduct of `ℤ` copies of the terminal sheaf.** -/
noncomputable def constantIntegerSheafIso :
    (constantSheaf J (Type m)).obj (ULift.{m} ℤ) ≅ ∐ fun _ : ℤ => ⊤_ (Sheaf J (Type m)) :=
  haveI : PreservesColimit (Discrete.functor fun _ : ℤ => PUnit.{m + 1})
      (constantSheaf J (Type m)) := preservesColimit_constantSheaf J _
  (constantSheaf J (Type m)).mapIso integerCoproductIso.symm ≪≫
    PreservesCoproduct.iso (constantSheaf J (Type m)) (fun _ : ℤ => PUnit.{m + 1}) ≪≫
      Sigma.mapIso fun _ : ℤ => constantUnitSheafIso J

/-- The constant integer `i`, read off the comparison of the constant sheaf of integers with the
coproduct of terminal sheaves: it is the summand `i`. -/
theorem constantIntegerSheafIso_ι (i : ℤ) :
    (constantSheaf J (Type m)).map (↾fun _ : PUnit.{m + 1} => (⟨i⟩ : ULift.{m} ℤ)) ≫
        (constantIntegerSheafIso J).hom =
      (constantUnitSheafIso J).hom ≫ Sigma.ι (fun _ : ℤ => ⊤_ (Sheaf J (Type m))) i := by
  have : PreservesColimit (Discrete.functor fun _ : ℤ => PUnit.{m + 1})
      (constantSheaf J (Type m)) := preservesColimit_constantSheaf J _
  rw [← integerCoproductIso_ι i, Functor.map_comp]
  simp [constantIntegerSheafIso, constantUnitSheafIso, Category.assoc,
    ← Functor.map_comp_assoc, reassoc_of% map_ι_preservesCoproductIso_hom]

/-- The degree-`i` section of the constant sheaf of integers, as a morphism out of the terminal
sheaf. -/
noncomputable def terminalDegree (i : ℤ) :
    ⊤_ (Sheaf J (Type m)) ⟶ (constantSheaf J (Type m)).obj (ULift.{m} ℤ) :=
  (constantUnitSheafIso J).inv ≫
    (constantSheaf J (Type m)).map (↾fun _ : PUnit.{m + 1} => (⟨i⟩ : ULift.{m} ℤ))

/-- The degree-`i` section of the constant sheaf of integers is the summand `i` of the coproduct
of terminal sheaves. -/
theorem terminalDegree_iso (i : ℤ) :
    terminalDegree J i ≫ (constantIntegerSheafIso J).hom =
      Sigma.ι (fun _ : ℤ => ⊤_ (Sheaf J (Type m))) i := by
  simp only [terminalDegree, Category.assoc, constantIntegerSheafIso_ι, Iso.inv_hom_id_assoc]

end ConstantSheaf

/-! ### The sheaf cut out by an equation between two morphisms of sheaves of sets -/

section EqFiber

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Two equalizers compared by a pair of isomorphisms intertwining the two parallel pairs. -/
noncomputable def equalizerCongrIso {D : Type*} [Category* D] {X Y X' Y' : D} {a b : X ⟶ Y}
    {a' b' : X' ⟶ Y'} [HasEqualizer a b] [HasEqualizer a' b'] (e : X ≅ X') (e' : Y ≅ Y')
    (ha : a ≫ e'.hom = e.hom ≫ a') (hb : b ≫ e'.hom = e.hom ≫ b') :
    equalizer a b ≅ equalizer a' b' where
  hom := equalizer.lift (equalizer.ι a b ≫ e.hom) (by
    simp only [Category.assoc, ← ha, ← hb]
    rw [← Category.assoc, ← Category.assoc, equalizer.condition])
  inv := equalizer.lift (equalizer.ι a' b' ≫ e.inv) (by
    apply (cancel_mono e'.hom).1
    simp only [Category.assoc, ha, hb, Iso.inv_hom_id_assoc]
    exact equalizer.condition a' b')
  hom_inv_id := by apply equalizer.hom_ext; simp [Category.assoc]
  inv_hom_id := by apply equalizer.hom_ext; simp [Category.assoc]

/-- The comparison of two equalizers is compatible with the two inclusions. -/
@[simp]
theorem equalizerCongrIso_hom_comp_ι {D : Type*} [Category* D] {X Y X' Y' : D} {a b : X ⟶ Y}
    {a' b' : X' ⟶ Y'} [HasEqualizer a b] [HasEqualizer a' b'] (e : X ≅ X') (e' : Y ≅ Y')
    (ha : a ≫ e'.hom = e.hom ≫ a') (hb : b ≫ e'.hom = e.hom ≫ b') :
    (equalizerCongrIso e e' ha hb).hom ≫ equalizer.ι a' b' = equalizer.ι a b ≫ e.hom :=
  equalizer.lift_ι _ _

/-- The presheaf of local sections on which two morphisms of sheaves of sets agree. -/
def eqFiber {F G : Sheaf J (Type m)} (a b : F ⟶ G) : Cᵒᵖ ⥤ Type m where
  obj U := { s : F.obj.obj U // a.hom.app U s = b.hom.app U s }
  map {U V} f := ↾fun s =>
    ⟨F.obj.map f s.1, by
      refine Eq.trans (a.hom.naturality_apply f s.1)
        (Eq.trans ?_ (b.hom.naturality_apply f s.1).symm)
      exact congrArg (G.obj.map f) s.2⟩
  map_id U := by
    ext s
    exact Functor.map_id_apply F.obj U s.1
  map_comp f g := by
    ext s
    exact Functor.map_comp_apply F.obj f g s.1

/-- The equation fibre, as a fork of the two morphisms in presheaves. -/
noncomputable def eqFiberFork {F G : Sheaf J (Type m)} (a b : F ⟶ G) : Fork a.hom b.hom :=
  Fork.ofι (P := eqFiber a b)
    { app U := ↾fun s => s.1
      naturality _ _ _ := rfl }
    (by ext U s; exact s.2)

/-- The fork exhibiting the equation fibre is a limit fork. -/
noncomputable def eqFiberForkIsLimit {F G : Sheaf J (Type m)} (a b : F ⟶ G) :
    IsLimit (eqFiberFork a b) :=
  Fork.IsLimit.mk _
    (fun t =>
      { app U := ↾fun s => ⟨t.ι.app U s, congrArg (fun k => k.app U s) t.condition⟩
        naturality {U V} r := by
          ext s
          apply Subtype.ext
          exact t.ι.naturality_apply r s })
    (fun t => by
      ext U s
      rfl)
    (fun t k hk => by
      ext U s
      exact Subtype.ext (congrArg (fun z => z.app U s) hk))

/-- The equation fibre of two morphisms of sheaves of sets is a sheaf: it is a limit of a
diagram of sheaves. -/
theorem eqFiber_isSheaf {F G : Sheaf J (Type m)} (a b : F ⟶ G) :
    Presheaf.IsSheaf J (eqFiber a b) :=
  have e := diagramIsoParallelPair (parallelPair a b ⋙ sheafToPresheaf J (Type m))
  Sheaf.isSheaf_of_isLimit (parallelPair a b)
    ((Cone.postcompose e.inv).obj (eqFiberFork a b))
    ((IsLimit.postcomposeInvEquiv e (eqFiberFork a b)).symm (eqFiberForkIsLimit a b))

/-- The sheaf of local sections on which two morphisms of sheaves of sets agree. -/
noncomputable abbrev eqFiberSheaf {F G : Sheaf J (Type m)} (a b : F ⟶ G) : Sheaf J (Type m) :=
  ⟨eqFiber a b, eqFiber_isSheaf a b⟩

/-- The equation fibre of two morphisms of sheaves of sets is their equalizer, taken in the
category of sheaves. -/
noncomputable def eqFiberSheafIso {F G : Sheaf J (Type m)} (a b : F ⟶ G) :
    eqFiberSheaf a b ≅ equalizer a b where
  hom := equalizer.lift ⟨(eqFiberFork a b).ι⟩ (Sheaf.hom_ext (eqFiberFork a b).condition)
  inv := ⟨(eqFiberForkIsLimit a b).lift
    (Fork.ofι (equalizer.ι a b).hom
      (congrArg (fun k => k.hom) (equalizer.condition a b)))⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    apply Fork.IsLimit.hom_ext (eqFiberForkIsLimit a b)
    change (equalizer.lift (f := a) (g := b)
        (⟨(eqFiberFork a b).ι⟩ : eqFiberSheaf a b ⟶ F) _).hom ≫
      (eqFiberForkIsLimit a b).lift
        (Fork.ofι (equalizer.ι a b).hom
          (congrArg (fun k => k.hom) (equalizer.condition a b))) ≫
        (eqFiberFork a b).ι = (eqFiberFork a b).ι
    rw [Fork.IsLimit.lift_ι]
    exact congrArg (fun k : eqFiberSheaf a b ⟶ F => k.hom)
      (equalizer.lift_ι (f := a) (g := b)
        (⟨(eqFiberFork a b).ι⟩ : eqFiberSheaf a b ⟶ F)
        (Sheaf.hom_ext (eqFiberFork a b).condition))
  inv_hom_id := by
    apply equalizer.hom_ext
    apply Sheaf.hom_ext
    change _ ≫ ((equalizer.lift _ _ ≫ equalizer.ι a b).hom) = _
    rw [equalizer.lift_ι]
    exact Fork.IsLimit.lift_ι (eqFiberForkIsLimit a b)

/-- The inclusion of the equation fibre into the source sheaf. -/
noncomputable def eqFiberι {F G : Sheaf J (Type m)} (a b : F ⟶ G) : eqFiberSheaf a b ⟶ F :=
  ⟨(eqFiberFork a b).ι⟩

/-- On sections, the inclusion of the equation fibre takes a section to its underlying section
of the source sheaf. -/
@[simp]
theorem eqFiberι_app {F G : Sheaf J (Type m)} (a b : F ⟶ G) (U : Cᵒᵖ)
    (s : (eqFiber a b).obj U) : (eqFiberι a b).hom.app U s = s.1 :=
  rfl

/-- The comparison with the equalizer is compatible with the two inclusions. -/
@[simp]
theorem eqFiberSheafIso_hom_comp_ι {F G : Sheaf J (Type m)} (a b : F ⟶ G) :
    (eqFiberSheafIso a b).hom ≫ equalizer.ι a b = eqFiberι a b :=
  equalizer.lift_ι _ _

/-- The comparison with the equalizer is compatible with the two inclusions, read backwards. -/
@[simp]
theorem eqFiberSheafIso_inv_comp_ι {F G : Sheaf J (Type m)} (a b : F ⟶ G) :
    (eqFiberSheafIso a b).inv ≫ eqFiberι a b = equalizer.ι a b := by
  rw [← eqFiberSheafIso_hom_comp_ι, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The inclusion of the equation fibre is a monomorphism: it is the equalizer inclusion read
through `Stacks.eqFiberSheafIso`. -/
instance mono_eqFiberι {F G : Sheaf J (Type m)} (a b : F ⟶ G) : Mono (eqFiberι a b) := by
  rw [← eqFiberSheafIso_hom_comp_ι]
  infer_instance

/-- A functor out of the sheaves of sets preserving the relevant equalizer carries an equation
fibre to the equation fibre of the images. -/
noncomputable def eqFiberSheafPreservesIso {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} (Φ : Sheaf J (Type m) ⥤ Sheaf J₁ (Type m₁))
    {F G : Sheaf J (Type m)} (a b : F ⟶ G) [Limits.PreservesLimit (parallelPair a b) Φ] :
    Φ.obj (eqFiberSheaf a b) ≅ eqFiberSheaf (Φ.map a) (Φ.map b) :=
  Φ.mapIso (eqFiberSheafIso a b) ≪≫ PreservesEqualizer.iso Φ a b ≪≫
    (eqFiberSheafIso (Φ.map a) (Φ.map b)).symm

/-- **The comparison of equation fibres is the one compatible with the two inclusions**, which
together with `Stacks.mono_eqFiberι` is what makes every naturality square for it checkable. -/
theorem eqFiberSheafPreservesIso_hom_comp_ι {C₁ : Type u₁} [Category.{v₁} C₁]
    {J₁ : GrothendieckTopology C₁} (Φ : Sheaf J (Type m) ⥤ Sheaf J₁ (Type m₁))
    {F G : Sheaf J (Type m)} (a b : F ⟶ G) [Limits.PreservesLimit (parallelPair a b) Φ] :
    (eqFiberSheafPreservesIso Φ a b).hom ≫ eqFiberι (Φ.map a) (Φ.map b) =
      Φ.map (eqFiberι a b) := by
  rw [eqFiberSheafPreservesIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    Iso.symm_hom, eqFiberSheafIso_inv_comp_ι, PreservesEqualizer.iso_hom,
    equalizerComparison_comp_π, Functor.mapIso_hom, ← Functor.map_comp,
    eqFiberSheafIso_hom_comp_ι]

/-- Two equation fibres compared by a pair of isomorphisms intertwining the two parallel
pairs. -/
noncomputable def eqFiberSheafCongrIso {F G F' G' : Sheaf J (Type m)} {a b : F ⟶ G}
    {a' b' : F' ⟶ G'} (e : F ≅ F') (e' : G ≅ G') (ha : a ≫ e'.hom = e.hom ≫ a')
    (hb : b ≫ e'.hom = e.hom ≫ b') : eqFiberSheaf a b ≅ eqFiberSheaf a' b' :=
  eqFiberSheafIso a b ≪≫ equalizerCongrIso e e' ha hb ≪≫ (eqFiberSheafIso a' b').symm

/-- The comparison of two equation fibres is compatible with the two inclusions. -/
theorem eqFiberSheafCongrIso_hom_comp_ι {F G F' G' : Sheaf J (Type m)} {a b : F ⟶ G}
    {a' b' : F' ⟶ G'} (e : F ≅ F') (e' : G ≅ G') (ha : a ≫ e'.hom = e.hom ≫ a')
    (hb : b ≫ e'.hom = e.hom ≫ b') :
    (eqFiberSheafCongrIso e e' ha hb).hom ≫ eqFiberι a' b' = eqFiberι a b ≫ e.hom := by
  rw [eqFiberSheafCongrIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    Iso.symm_hom, eqFiberSheafIso_inv_comp_ι, equalizerCongrIso_hom_comp_ι,
    ← Category.assoc, eqFiberSheafIso_hom_comp_ι]

end EqFiber

/-! ### The sheaf of degree-`i` local sections -/

section DegreeFiber

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J (Type m)]

/-- The morphism of sheaves of sets carrying every local section to the constant degree `i`. A
local section of `S` has degree `i` exactly when the degree morphism agrees with this one on
it. -/
noncomputable def constantDegreeMap (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    S.sheaf ⟶ (constantSheaf J (Type m)).obj (ULift.{m} ℤ) where
  hom :=
    { app U := ↾fun _ => (toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{m} ℤ))).app U ⟨i⟩
      naturality {U V} f := by
        ext s
        exact (toSheafify J ((Functor.const Cᵒᵖ).obj (ULift.{m} ℤ))).naturality_apply f
          (ULift.up (α := ℤ) i) }

/-- The presheaf of degree-`i` local sections of a sheaf of graded sets: the equation fibre of
the degree morphism against the constant `i`. -/
noncomputable def degreeFiber (S : SheafOfGradedSets.{m} J) (i : ℤ) : Cᵒᵖ ⥤ Type m :=
  eqFiber S.degree (constantDegreeMap S i)

/-- The sections of the degree-`i` fibre are the local sections of degree `i`. -/
theorem degreeFiber_obj (S : SheafOfGradedSets.{m} J) (i : ℤ) (U : Cᵒᵖ) :
    (degreeFiber S i).obj U = { s : S.sheaf.obj.obj U // S.HasDegree U s i } :=
  rfl

/-- The degree-`i` fibre of a sheaf of graded sets is a sheaf: it is a limit of a diagram of
sheaves. -/
theorem degreeFiber_isSheaf (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    Presheaf.IsSheaf J (degreeFiber S i) :=
  eqFiber_isSheaf S.degree (constantDegreeMap S i)

/-- The sheaf of degree-`i` local sections of a sheaf of graded sets. -/
noncomputable abbrev degreeFiberSheaf (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    Sheaf J (Type m) :=
  eqFiberSheaf S.degree (constantDegreeMap S i)

/-- The underlying presheaf of the sheaf of degree-`i` local sections. -/
theorem degreeFiberSheaf_obj (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    (degreeFiberSheaf S i).obj = degreeFiber S i :=
  rfl

/-- The sheaf of degree-`i` local sections is the equalizer of the degree morphism and the
constant `i`, taken in the category of sheaves. -/
noncomputable def degreeFiberSheafIso (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    degreeFiberSheaf S i ≅ equalizer S.degree (constantDegreeMap S i) :=
  eqFiberSheafIso S.degree (constantDegreeMap S i)

/-- The constant degree-`i` morphism factors through the terminal sheaf. -/
theorem constantDegreeMap_eq_terminalDegree (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    constantDegreeMap S i = terminal.from S.sheaf ≫ terminalDegree J i := by
  let z : S.sheaf ⟶ (constantSheaf J (Type m)).obj PUnit.{m + 1} :=
    ⟨{ app U := ↾fun _ =>
          (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{m + 1})).app U PUnit.unit
       naturality {U V} r := by
         ext s
         exact (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{m + 1})).naturality_apply r
           PUnit.unit }⟩
  have hz : z = terminal.from S.sheaf ≫ (constantUnitSheafIso J).inv :=
    (cancel_mono (constantUnitSheafIso J).hom).1 (terminalIsTerminal.hom_ext _ _)
  rw [terminalDegree, ← Category.assoc, ← hz]
  ext U s
  exact congrArg (fun k => k.app U PUnit.unit) (toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (↾fun _ : PUnit.{m + 1} => (⟨i⟩ : ULift.{m} ℤ))))

end DegreeFiber

/-! ### The inverse image of a sheaf of graded sets -/

section InverseImage

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J (Type m)]
  {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  [HasSheafify J₁ (Type m₁)]

/-- **The inverse image of the constant sheaf of integers along a morphism of topoi is the
constant sheaf of integers.** Both are the coproduct of `ℤ` copies of the terminal sheaf, and
the inverse image preserves that coproduct, being a left adjoint, and the terminal object, being
left exact. -/
noncomputable def inverseImageConstantIntegerIso
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m))) :
    f.inverseImage.obj ((constantSheaf J (Type m)).obj (ULift.{m} ℤ)) ≅
      (constantSheaf J₁ (Type m₁)).obj (ULift.{m₁} ℤ) :=
  f.inverseImage.mapIso (constantIntegerSheafIso J) ≪≫
    PreservesCoproduct.iso f.inverseImage (fun _ : ℤ => ⊤_ (Sheaf J (Type m))) ≪≫
      Sigma.mapIso (fun _ : ℤ => PreservesTerminal.iso f.inverseImage) ≪≫
        (constantIntegerSheafIso J₁).symm

/-- **The inverse image of a sheaf of graded sets along a morphism of topoi**: the inverse image
of the underlying sheaf of sets, graded by the inverse image of the degree morphism read through
the identification of the two constant sheaves of integers. -/
noncomputable def SheafOfGradedSets.inverseImage
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) : SheafOfGradedSets.{m₁} J₁ where
  sheaf := f.inverseImage.obj S.sheaf
  degree := f.inverseImage.map S.degree ≫ (inverseImageConstantIntegerIso f).hom

/-- The sheaf of sets underlying the inverse image of a sheaf of graded sets. -/
@[simp]
theorem SheafOfGradedSets.inverseImage_sheaf
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) :
    (SheafOfGradedSets.inverseImage f S).sheaf = f.inverseImage.obj S.sheaf :=
  rfl

/-- The degree morphism of the inverse image of a sheaf of graded sets. -/
@[simp]
theorem SheafOfGradedSets.inverseImage_degree
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) :
    (SheafOfGradedSets.inverseImage f S).degree =
      f.inverseImage.map S.degree ≫ (inverseImageConstantIntegerIso f).hom :=
  rfl

/-- The inverse image of the degree-`i` section of the constant sheaf of integers is the
degree-`i` section on the target. -/
theorem inverseImage_terminalDegree
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m))) (i : ℤ) :
    f.inverseImage.map (terminalDegree J i) ≫ (inverseImageConstantIntegerIso f).hom =
      (PreservesTerminal.iso f.inverseImage).hom ≫ terminalDegree J₁ i := by
  apply (cancel_mono (constantIntegerSheafIso J₁).hom).1
  simp only [Category.assoc, terminalDegree_iso]
  simp [inverseImageConstantIntegerIso, Category.assoc, ← Functor.map_comp_assoc,
    terminalDegree_iso, reassoc_of% map_ι_preservesCoproductIso_hom]

/-- The sheaf of sets underlying the inverse image of a sheaf of graded sets **is** the inverse
image of the underlying sheaf of sets, so the comparison is the identity. -/
noncomputable def inverseImageSheafIso
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) :
    f.inverseImage.obj S.sheaf ≅ (SheafOfGradedSets.inverseImage f S).sheaf :=
  Iso.refl _

/-- The comparison `inverseImageSheafIso` is the identity. -/
theorem inverseImageSheafIso_hom
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) :
    (inverseImageSheafIso f S).hom = 𝟙 (f.inverseImage.obj S.sheaf) :=
  rfl

/-- The inverse image of the constant-degree-`i` morphism of a sheaf of graded sets is, up to
the comparisons, the constant-degree-`i` morphism of its inverse image. -/
theorem inverseImage_constantDegreeMap
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    f.inverseImage.map (constantDegreeMap S i) ≫ (inverseImageConstantIntegerIso f).hom =
      (inverseImageSheafIso f S).hom ≫
        constantDegreeMap (SheafOfGradedSets.inverseImage f S) i := by
  refine Eq.trans ?_ (Category.id_comp
    (constantDegreeMap (SheafOfGradedSets.inverseImage f S) i)).symm
  rw [constantDegreeMap_eq_terminalDegree, Functor.map_comp, Category.assoc,
    inverseImage_terminalDegree, ← Category.assoc, constantDegreeMap_eq_terminalDegree]
  exact Eq.trans (congrArg (fun k => k ≫ terminalDegree J₁ i)
      (terminalIsTerminal.hom_ext
        (f.inverseImage.map (terminal.from S.sheaf) ≫ (PreservesTerminal.iso f.inverseImage).hom)
        (terminal.from (f.inverseImage.obj S.sheaf))))
    (Category.id_comp _).symm

/-- The degree morphism of the inverse image, as an intertwining square. -/
theorem inverseImage_degree
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) :
    f.inverseImage.map S.degree ≫ (inverseImageConstantIntegerIso f).hom =
      (inverseImageSheafIso f S).hom ≫
        (SheafOfGradedSets.inverseImage f S).degree :=
  (Category.id_comp (SheafOfGradedSets.inverseImage f S).degree).symm

/-- **The grading survives the inverse image, degree by degree.** The inverse image of the sheaf
of degree-`i` local sections of `S` is the sheaf of degree-`i` local sections of the inverse
image of `S`: both are an equalizer of the degree morphism against the constant `i`, the inverse
image preserves that equalizer, being left exact, and it carries the one constant `i` to the
other because the constant `i` factors through the terminal sheaf. -/
noncomputable def inverseImageDegreeFiberIso
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    f.inverseImage.obj (degreeFiberSheaf S i) ≅
      degreeFiberSheaf (SheafOfGradedSets.inverseImage f S) i :=
  eqFiberSheafPreservesIso f.inverseImage S.degree (constantDegreeMap S i) ≪≫
    eqFiberSheafCongrIso (inverseImageSheafIso f S) (inverseImageConstantIntegerIso f)
      (inverseImage_degree f S) (inverseImage_constantDegreeMap f S i)

/-- **The comparison identifying the inverse image of the degree-`i` fibre is the one
compatible with the two inclusions**, which together with `Stacks.mono_eqFiberι` is what makes
its naturality checkable. The right-hand comparison `inverseImageSheafIso` is an identity
morphism; it is kept so that the two sides have the same type on the nose. -/
theorem inverseImageDegreeFiberIso_hom_comp_ι
    (f : MorphismOfTopoi (Sheaf J₁ (Type m₁)) (Sheaf J (Type m)))
    (S : SheafOfGradedSets.{m} J) (i : ℤ) :
    (inverseImageDegreeFiberIso f S i).hom ≫
        eqFiberι (SheafOfGradedSets.inverseImage f S).degree
          (constantDegreeMap (SheafOfGradedSets.inverseImage f S) i) =
      f.inverseImage.map (eqFiberι S.degree (constantDegreeMap S i)) ≫
        (inverseImageSheafIso f S).hom := by
  rw [inverseImageDegreeFiberIso, Iso.trans_hom, Category.assoc,
    eqFiberSheafCongrIso_hom_comp_ι, ← Category.assoc,
    eqFiberSheafPreservesIso_hom_comp_ι]

end InverseImage

end Stacks

end
