module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor

/-!
# The degree-zero twist of a coherent triple is the triple itself

The induction step of [Stacks, Tag 0F27] twists a short exact sequence of coherent triples by
`L^{⊗ n}`, and for the twisted sequence to begin at `T ⊗ L^{⊗ n}` the untwisted one has to begin
at `T` itself. What the cokernel machinery produces instead begins at the *degree-zero* twist
`T ⊗ L^{⊗ 0}`, so the sequence has to be moved along the identification of that twist with the
triple -- which is the right unit constraint of the tensor product on each member, there being
nothing else it could be: the degree-zero tensor power of an invertible module **is** the
structure sheaf (`Stacks.SheafOfModules.TensorPower.tensorPower_zero`, an equality by `rfl`), so
`Stacks.Algebraization.tensorPowScheme X L 0` is the monoidal unit on the nose.

What makes the identification a morphism of *coherent triples* rather than a pair of unrelated
isomorphisms of modules is its compatibility square with the inverse-image comparison of
[Stacks, Tag 01CD], and that is the content of this file.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.twistZZeroHom`: **the degree-zero twist of a coherent
  triple, identified with the triple itself**, as a morphism of coherent triples
  `T ⊗ L^{⊗ 0} ⟶ T` whose two members are the right unitors.

## Main results

* `Stacks.Algebraization.pullbackTensorModulesIso_rightUnitor`: **[Stacks, Tag 01CD] is
  compatible with the right unit constraint of [Stacks, Tag 01CA]**, at the scheme spelling.
* `Stacks.Algebraization.alphaPow_zero`: **the degree-zero tensor power of the identification of
  an invertible coherent triple is the comparison of the two structure sheaves.**
* `Stacks.Algebraization.rightUnitor_whiskerLeft_square`: the naturality of the right unitor
  against a left whiskering, in an abstract monoidal category.
* `Stacks.Algebraization.alpha_twistZ_zero_rightUnitor`: **the right unitors carry the
  identification of `T ⊗ L^{⊗ 0}` to the identification of `T`** -- the compatibility square of
  the morphism of triples.
* `Stacks.Algebraization.CoherentTriple.isIso_twistZZeroHom`: both members of the degree-zero
  identification are isomorphisms, which is the form in which
  `Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` and
  `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom` consume an identification
  of coherent triples.

## Implementation notes

The route to the right-unitor square is the one
`Stacks.Algebraization.pullbackTensorModulesIso_associator` and
`Stacks.Algebraization.pullbackTensorModulesIso_braiding` take, and the proof is the same single
term: the abstract statement is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor`, the monoidal structure it
is about is `Stacks.Algebraization.strictModulesMonoidal` by
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`, which is `rfl`, and the comparison of the
units it mentions -- `Stacks.PullbackTensorCoherence.pullbackUnitComparison`, i.e.
`Stacks.PullbackAlgebra.unitComparison` -- is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, the datum
`Stacks.Algebraization.pullbackTensorPowSchemeIso` is built with. Both are
`SheafOfModules.pullbackObjUnitToUnit` of the structure morphism, so no bridge between the two
unit comparisons is needed; this is what makes `alphaPow_zero` available in the shape the square
consumes.

**Why the assembly of the square is split in two.** As in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistBraiding`, the two routes around
the square of a coherent triple reach the modules of the punctured closed fibre by different
spellings of that scheme -- `Stacks.Algebraization.CoherentTriple.alpha` spells it as the source
of `AlgebraicGeometry.morphismRestrict`, while a statement about `(puncturedClosedFibre A f).ι`
spells it `(Stacks.Algebraization.puncturedClosedFibre A f).toScheme` -- so deciding the two
monoidal instances equal costs real heartbeats, and the pasting pays that cost once for each side
of the square. The two sides are therefore pasted in two declarations,
`Stacks.Algebraization.comp_eq_of_unitor_square_left` and
`..._right`, each applied in a `private` definition with no ascribed type, so that each gets a
heartbeat budget of its own; this is the idiom recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSuccessor`. The generic
rearrangements are stated for an abstract category because in `X.Modules` a rewrite along
`CategoryTheory.Category.assoc` does not fire.

The two pasting lemmas are not instances of
`Stacks.Algebraization.comp_eq_of_inner_squares` and
`Stacks.Algebraization.comp_eq_of_outer_square`: those paste a five-factor composite, which is
the shape of the successor and reordering squares, whereas the right-unitor square has a factor
fewer on each side -- there is no whiskered tensor-power comparison between the inverse-image
comparison and the unitor.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

attribute [local instance] strictModulesMonoidal

/-! ### The right unitor and the inverse-image comparison -/

/-- **[Stacks, Tag 01CD] is compatible with the right unit constraint of [Stacks, Tag 01CA]**,
at the scheme spelling: the comparison of the inverse image of a tensor product with the tensor
product of the inverse images carries the right unitor to the right unitor, the unit object being
matched by `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor`, read at
`Stacks.Algebraization.strictModulesMonoidal` exactly as
`Stacks.Algebraization.pullbackTensorModulesIso_associator` reads the associator coherence. -/
public theorem pullbackTensorModulesIso_rightUnitor {X S : Scheme.{u}} (g : X ⟶ S)
    (A : S.Modules) :
    (Scheme.Modules.pullback g).map (ρ_ A).hom =
      (pullbackTensorModulesIso g A (𝟙_ S.Modules)).hom ≫
        (((Scheme.Modules.pullback g).obj A : X.Modules) ◁
          (Scheme.Modules.pullbackUnitIso g).hom) ≫
          (ρ_ ((Scheme.Modules.pullback g).obj A : X.Modules)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor g.toLRSHom.toShHom A

/-! ### The degree-zero power of the identification of an invertible triple -/

/-- Congruence for a three-fold composite. Isolated as a lemma because the statement it is used
in rewrites the *objects* of the composite -- the degree-zero tensor powers, into the structure
sheaves -- and such a goal is not type-correct at the `implicit` transparency at which `rw`
checks its motive; inside this lemma the objects are abstract and no rewriting of them
happens. -/
private theorem comp_congr₃ {C : Type*} [Category C] {X Y Z W : C} {a a' : X ⟶ Y}
    {b b' : Y ⟶ Z} {c c' : Z ⟶ W} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') :
    a ≫ b ≫ c = a' ≫ b' ≫ c' := by rw [h₁, h₂, h₃]

/-- An identity in the middle of a three-fold composite is absorbed. Isolated for the same
reason as `comp_congr₃`. -/
private theorem comp_id_comp {C : Type*} [Category C] {X Y W : C} (a : X ⟶ Y) (c : Y ⟶ W) :
    a ≫ 𝟙 Y ≫ c = a ≫ c := by rw [Category.id_comp]

/-- **The degree-zero tensor power of the identification of an invertible coherent triple is the
comparison of the two structure sheaves.** Both factors of
`Stacks.Algebraization.IsInvertibleTriple.alphaPow` degenerate in degree zero: the inverse-image
comparison of the tensor powers is the comparison of the structure sheaves
(`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero`) and the comparison of the powers of
two isomorphic modules is the identity
(`Stacks.SheafOfModules.TensorPower.tensorPowerCongr_zero`). -/
public theorem alphaPow_zero {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (hL.alphaPow 0).hom =
      (Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).hom ≫
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  let := isEquivalence_tensorRightFunctor_of_isInvertibleModule
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F
  let := isEquivalence_tensorRightFunctor_of_isInvertibleModule (closedFibre A f) L.F₀
  let := isEquivalence_tensorRightFunctor_of_isInvertibleModule
    (puncturedClosedFibre A f).toScheme
    ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).obj L.F)
  let := isEquivalence_tensorRightFunctor_of_isInvertibleModule
    (puncturedClosedFibre A f).toScheme
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀)
  have h1 : pullbackTensorPowSchemeIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) L.F 0 =
      Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) :=
    Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero _ _ _ _ _ _ _ _
  have h2 : pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ 0 =
      Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι :=
    Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_zero _ _ _ _ _ _ _ _
  have h3 : tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha 0 = Iso.refl _ :=
    Stacks.SheafOfModules.TensorPower.tensorPowerCongr_zero
      (puncturedClosedFibre A f).toScheme.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (puncturedClosedFibre A f).toScheme)
      L.alpha
  have hdef : (hL.alphaPow 0).hom =
      (pullbackTensorPowSchemeIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) L.F 0).hom ≫
        (tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha 0).hom ≫
        (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ 0).inv := rfl
  exact hdef.trans ((comp_congr₃ (congrArg Iso.hom h1) (congrArg Iso.hom h3)
    (congrArg Iso.inv h2)).trans (comp_id_comp _ _))

/-! ### Generic rearrangements -/

/-- **The naturality of the right unitor against a left whiskering.** Left whiskering a morphism
into the unit, followed by the right unitor and a morphism, is the tensor product of that morphism
with the whiskered one, followed by the other whiskering and the other right unitor. Stated for an
abstract monoidal category, because in `X.Modules` a rewrite along
`CategoryTheory.Category.assoc` does not fire. -/
public theorem rightUnitor_whiskerLeft_square {M : Type*} [Category M] [MonoidalCategory M]
    {Ak Aj Pk Pj : M} (a : Ak ⟶ Aj) (uk : Pk ⟶ 𝟙_ M) (uj : Pj ≅ 𝟙_ M) (d : Pk ⟶ Pj)
    (hd : d = uk ≫ uj.inv) :
    (Ak ◁ uk) ≫ (ρ_ Ak).hom ≫ a = (a ⊗ₘ d) ≫ (Aj ◁ uj.hom) ≫ (ρ_ Aj).hom := by
  have hwl : (Aj ◁ (uk ≫ uj.inv)) ≫ (Aj ◁ uj.hom) = Aj ◁ uk := by
    rw [← MonoidalCategory.whiskerLeft_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc (Ak ◁ uk) ≫ (ρ_ Ak).hom ≫ a
      = ((Ak ◁ uk) ≫ (a ▷ 𝟙_ M)) ≫ (ρ_ Aj).hom := by
        simp only [Category.assoc]
        rw [MonoidalCategory.rightUnitor_naturality]
    _ = ((a ▷ Pk) ≫ (Aj ◁ uk)) ≫ (ρ_ Aj).hom := by rw [MonoidalCategory.whisker_exchange]
    _ = (a ▷ Pk) ≫ ((Aj ◁ (uk ≫ uj.inv)) ≫ (Aj ◁ uj.hom)) ≫ (ρ_ Aj).hom := by
        rw [hwl]
        simp only [Category.assoc]
    _ = (a ⊗ₘ d) ≫ (Aj ◁ uj.hom) ≫ (ρ_ Aj).hom := by
        rw [hd, MonoidalCategory.tensorHom_def]
        simp only [Category.assoc]

/-- The inner half of the pasting: a factorisation of the left-hand morphism through the
inverse-image comparison and the whiskered unitor, together with the middle square, gives the
left-hand route around the square of a coherent triple. -/
public theorem comp_eq_of_unitor_square_left {C : Type*} [Category C]
    {W V₁ Zk Y₁ Y₂ V₂ Zj : C} (m : W ⟶ Y₁) (α : Y₁ ⟶ Y₂) (P : W ⟶ V₁) (wk : V₁ ⟶ Zk)
    (rk : Zk ⟶ Y₁) (t : V₁ ⟶ V₂) (wj : V₂ ⟶ Zj) (rj : Zj ⟶ Y₂)
    (hk : m = P ≫ wk ≫ rk) (hmid : wk ≫ rk ≫ α = t ≫ wj ≫ rj) :
    m ≫ α = P ≫ t ≫ wj ≫ rj := by
  rw [hk, Category.assoc, Category.assoc, hmid]

/-- The outer half of the pasting: the left-hand route and the factorisation of the second
inverse-image comparison paste to the whole square. -/
public theorem comp_eq_of_unitor_square_right {C : Type*} [Category C]
    {W V₁ V₂ Vj Y₂ Zj : C} (e : W ⟶ Y₂) (P : W ⟶ V₁) (t : V₁ ⟶ V₂) (wj : V₂ ⟶ Zj)
    (rj : Zj ⟶ Y₂) (Q : Vj ≅ V₂) (m' : Vj ⟶ Y₂)
    (h : e = P ≫ t ≫ wj ≫ rj) (hj : m' = Q.hom ≫ wj ≫ rj) :
    e = P ≫ t ≫ Q.inv ≫ m' := by
  rw [h, hj, Iso.inv_hom_id_assoc]

/-! ### The compatibility square of the degree-zero identification -/

/-- The middle square of the degree-zero identification: the naturality of the right unitor,
`Stacks.Algebraization.rightUnitor_whiskerLeft_square`, read against
`Stacks.Algebraization.alphaPow_zero`. Split off into its own declaration, proved in term
mode, so that this application gets a heartbeat budget of its own; see the implementation notes
of this file. -/
private theorem alpha_twistZ_zero_rightUnitor_hmid {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).obj T.F ◁
        (Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).hom ≫
      (ρ_ ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj T.F)).hom ≫ T.alpha.hom =
    (T.alpha.hom ⊗ₘ (hL.alphaPow 0).hom) ≫
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀ ◁
          (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).hom ≫
        (ρ_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)).hom :=
  have := hL.invertible_F
  have := hL.invertible_F₀
  rightUnitor_whiskerLeft_square T.alpha.hom
    (Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).hom
    (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι)
    (hL.alphaPow 0).hom (alphaPow_zero hL)

/-- The left-hand half of the assembly of
`Stacks.Algebraization.alpha_twistZ_zero_rightUnitor`: the middle square pasted against the
right-unitor factorisation on the punctured-spectrum side. Split off for the same reason as
`alpha_twistZ_zero_rightUnitor_hmid`. -/
private theorem alpha_twistZ_zero_rightUnitor_left {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map (ρ_ T.F).hom ≫ T.alpha.hom =
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F
          (𝟙_ (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)).hom ≫
      (T.alpha.hom ⊗ₘ (hL.alphaPow 0).hom) ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀ ◁
            (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).hom ≫
          (ρ_ ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)).hom :=
  have := hL.invertible_F
  have := hL.invertible_F₀
  comp_eq_of_unitor_square_left _ _ _ _ _ _ _ _
    (pullbackTensorModulesIso_rightUnitor (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)) T.F)
    (alpha_twistZ_zero_rightUnitor_hmid T hL)

/-- The outer assembly of `Stacks.Algebraization.alpha_twistZ_zero_rightUnitor`: the left-hand
half pasted against the right-unitor factorisation on the closed-fibre side. Split from
`alpha_twistZ_zero_rightUnitor_left` so that each of the two sides of the square gets a heartbeat
budget of its own; see the implementation notes of this file. -/
private theorem alpha_twistZ_zero_rightUnitor_aux {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map (ρ_ T.F).hom ≫ T.alpha.hom =
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F
          (𝟙_ (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)).hom ≫
      (T.alpha.hom ⊗ₘ (hL.alphaPow 0).hom) ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
          (𝟙_ (closedFibre A f).Modules)).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (ρ_ T.F₀).hom :=
  have := hL.invertible_F
  have := hL.invertible_F₀
  comp_eq_of_unitor_square_right _ _ _ _ _ _ _
    (alpha_twistZ_zero_rightUnitor_left T hL)
    (pullbackTensorModulesIso_rightUnitor (puncturedClosedFibre A f).ι T.F₀)

/-- **The right unitors carry the identification of `T ⊗ L^{⊗ 0}` to the identification of
`T`.** This is the compatibility square that makes the degree-zero identification an isomorphism
of coherent triples rather than of each member separately: it is
`Stacks.Algebraization.pullbackTensorModulesIso_rightUnitor` in each of the two routes around the
square of a coherent triple, pasted around the naturality of the right unitor. -/
public theorem alpha_twistZ_zero_rightUnitor {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T : CoherentTriple A f) {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map (ρ_ T.F).hom ≫ T.alpha.hom =
      (T.twistZ L hL 0).alpha.hom ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map (ρ_ T.F₀).hom := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  rw [alpha_twistZ_eq_tensorHom T hL 0]
  exact alpha_twistZ_zero_rightUnitor_aux T hL

/-! ### The degree-zero identification as a morphism of coherent triples -/

/-- **The degree-zero twist of a coherent triple is the triple itself**, as a morphism of
coherent triples `T ⊗ L^{⊗ 0} ⟶ T`. Its two members are the right unitors of the two members --
the degree-zero tensor power of an invertible module being the structure sheaf on the nose -- and
its compatibility square is `Stacks.Algebraization.alpha_twistZ_zero_rightUnitor`.

Both members are isomorphisms
(`Stacks.Algebraization.CoherentTriple.isIso_twistZZeroHom`), so this is an isomorphism of
coherent triples in the sense the consumers of such an identification use --
`Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` and
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`, both of which ask for a
`Hom` with `IsIso` on each member. -/
public noncomputable def CoherentTriple.twistZZeroHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    (T.twistZ L hL 0).Hom T where
  onPunctured := (ρ_ T.F).hom
  onClosedFibre := (ρ_ T.F₀).hom
  compatible := alpha_twistZ_zero_rightUnitor T hL

/-- **Both members of the degree-zero identification are isomorphisms**, so
`Stacks.Algebraization.CoherentTriple.twistZZeroHom` is an isomorphism of coherent triples. -/
public theorem CoherentTriple.isIso_twistZZeroHom {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f} (hL : IsInvertibleTriple L) :
    IsIso (T.twistZZeroHom hL).onPunctured ∧ IsIso (T.twistZZeroHom hL).onClosedFibre :=
  ⟨inferInstanceAs (IsIso (ρ_ T.F).hom), inferInstanceAs (IsIso (ρ_ T.F₀).hom)⟩

end Stacks.Algebraization

end
