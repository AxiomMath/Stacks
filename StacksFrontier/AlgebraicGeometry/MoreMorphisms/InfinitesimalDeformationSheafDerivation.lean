module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPerturbation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# Infinitesimal deformations of maps: compatible derivation data, at sheaf level

Consider the commutative diagrams of [Stacks Project, Tag 04BY],
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> S₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> S₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
*without* assuming `X₂ → X₁` and `S₂ → S₁` étale. [Stacks Project, Tag 04BZ] observes that the
conclusion of [Stacks Project, Tag 04BY] still holds as soon as one is given both data
`θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` and `θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` whose associated
derivations `D_n = θ_n ∘ d_{X_n/S_n}` of Equation [Stacks Project, Tag 04BV] make the square
```
f_*𝒪_{X₂} ---f_*D₂---> f_*a_{2,*}𝒞_{T₂/T₂'}
    ^                           ^
   f^♯               induced by (h')^♯
    |                           |
  𝒪_{X₁} -----D₁------> a_{1,*}𝒞_{T₁/T₁'}
```
commute.

Unlike
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationGivenDerivation.lean`, which
proves this on global sections over affine ambient schemes, this file proves it for arbitrary
schemes: no scheme in either diagram is assumed affine and `θ₁`, `θ₂` are honest morphisms of
sheaves of modules.

## Main definitions

* `Stacks.Thickenings.derivationSectionι`: the value `D(y) = θ(d_{Y/S} y)` of the derivation of
  Equation [Stacks Project, Tag 04BV] attached to `θ`, read as a section of the defining ideal
  of the thickening inside the ambient structure sheaf.
* `Stacks.Thickenings.IsDerivationAction`: the relation "`b'` is `θ ⬝ a'`" of
  [Stacks Project, Tag 0CK1], expressed by the comorphism equation `(b')^♯ = (a')^♯ + D ∘ j^♯`
  that [Stacks Project, Tag 04FG] and [Stacks Project, Tag 02H5] characterise `θ ⬝ a'` by.

## Main results

* `Stacks.Thickenings.hom_ext_of_comp_eq_of_app`: two morphisms out of the ambient scheme of a
  thickening agreeing on the closed subscheme and on comorphisms are equal.
* `Stacks.Thickenings.conormalSectionι_smul` and
  `Stacks.Thickenings.conormalSectionι_naturality`: the inclusion of the conormal sections into
  the ambient structure sheaf carries a scalar out as a factor along `(a')^♯`, and is natural.
* `Stacks.Thickenings.derivationSectionι_add`,
  `Stacks.Thickenings.derivationSectionι_leibniz`,
  `Stacks.Thickenings.derivationSectionι_mul_derivationSectionι` and
  `Stacks.Thickenings.derivationSectionι_naturality`: the four properties that make `D` a
  square-zero perturbation of `a'` in the sense of
  `Stacks.Thickenings.SquareZeroPerturbation`.
* `Stacks.Thickenings.eq_of_isDerivationAction`: the uniqueness half of
  [Stacks Project, Tag 02H5] at sheaf level — at most one `b'` is `θ ⬝ a'`.
* `Stacks.Thickenings.derivationAction_comp_of_derivationSection_comm`: the conclusion of
  [Stacks Project, Tag 04BZ] for arbitrary schemes, for two lifts satisfying the comorphism
  equation.

## Implementation notes

The two lifts `θ₁ ⬝ a₁'` and `θ₂ ⬝ a₂'` enter the statement of
`Stacks.Thickenings.derivationAction_comp_of_derivationSection_comm` as morphisms `b₁'`, `b₂'`
*assumed* to satisfy `Stacks.Thickenings.IsDerivationAction`, which makes that statement the
general one: the relation pins its `b'` uniquely
(`Stacks.Thickenings.eq_of_isDerivationAction`) and it is the defining property of the notation
`θ ⬝ a'` in [Stacks Project, Tag 0CK1]. The existence half of [Stacks Project, Tag 02H5] at
sheaf level — that for every `θ` there *is* a `b'` with that relation — is
`Stacks.Thickenings.derivationActionSheaf` together with
`Stacks.Thickenings.isDerivationAction_derivationActionSheaf`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafAction.lean`, which
is built out of the four properties of `Stacks.Thickenings.derivationSectionι` proved here.
Because the two lifts are assumed here rather than constructed, the attribute for
[Stacks Project, Tag 04BZ] is not placed in this file: it goes on
`Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm` there, which is this
statement with both lifts the constructed `Stacks.Thickenings.derivationActionSheaf` and which
is deduced from the theorem below. Over affine ambient schemes the relation is satisfied by
`Stacks.Thickenings.derivationAction`, where the existence half is
`Stacks.Thickenings.existsUnique_derivationAction`.

`Stacks.Thickenings.IsDerivationAction` is the comorphism equation rather than a statement about
a difference derivation, because it needs nothing of the sheaf-level difference derivation of
[Stacks Project, Tag 04FG]; that derivation is
`Stacks.Thickenings.differenceDerivation` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationSheaf.lean`, which goes the
other way and produces a `θ` from a pair of lifts
(`Stacks.Thickenings.exists_isDerivationAction`). The equation
`(b')^♯ s = (a')^♯ s + D(j^♯ s)` *is* the assertion that the difference derivation of the pair
`(b', a')` is `D`, which is what the source's characterisation of `θ ⬝ a'` says; it is stated
section by section because the two comorphisms are ring maps and only their difference is
additive.

The derivation `D` is read inside the ambient structure sheaf, through the inclusion
`Stacks.Thickenings.firstOrderImmersionConormalSheafι` of the conormal sheaf of a first-order
thickening into `𝒪_{T'}`. That inclusion is a monomorphism, so this loses nothing; and the
right-hand vertical map "induced by `(h')^♯`" of the source's square is, read through it, the
ring map `(h')^♯` on ambient sections. That is exactly how the hypothesis of the affine case
`Stacks.Thickenings.derivationAction_comp_of_derivation_comm` is stated too.

Two morphisms `a'`, `b'` out of `T'` that restrict to the same map on `T` have the same
underlying continuous map, because the underlying map of a first-order thickening is surjective;
this is what makes the comorphism equation expressible at all, and the transports it needs are
restriction maps along equalities of opens. The category of opens is thin, so those transports
never have to be compared with one another by hand
(`Stacks.Thickenings.presheaf_map_eq`).

Three hypotheses of [Stacks Project, Tag 04BY] are not needed and are omitted rather than
carried unused: the morphism `k : S₂ ⟶ S₁` and the commutativity of the square of bases, and the
first-order thickening hypotheses on `j₁` and `j₂`. They enter [Stacks Project, Tag 04BY] only
through the construction of `θ₂` from `θ₁`. What is used is the right-hand half of the diagram
together with the two left-hand squares, which are what force the two sides of the conclusion to
agree on `T₂`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Opposite TopologicalSpace

universe u

namespace Stacks.Thickenings

/-! ### Two lifts of the same morphism have the same underlying map -/

variable {S T T' Y Y' : Scheme.{u}}

/-- Morphisms out of the ambient scheme of a thickening that agree after restriction to the
closed subscheme have the same underlying continuous map. -/
theorem base_eq_of_comp_eq {Z : Scheme.{u}} {i : T ⟶ T'} (hsurj : Function.Surjective i)
    {c d : T' ⟶ Z} (h : i ≫ c = i ≫ d) : c.base = d.base := by
  have h1 : ∀ y : T, c (i y) = d (i y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  refine TopCat.hom_ext (ContinuousMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := hsurj x
  exact h1 y

/-- The preimage of an open under two such morphisms is the same open. -/
theorem preimage_eq_of_comp_eq {Z : Scheme.{u}} {i : T ⟶ T'} (hsurj : Function.Surjective i)
    {c d : T' ⟶ Z} (h : i ≫ c = i ≫ d) (V : Z.Opens) : c ⁻¹ᵁ V = d ⁻¹ᵁ V := by
  rw [base_eq_of_comp_eq hsurj h]

/-- Two morphisms out of the ambient scheme of a thickening that agree after restriction to the
closed subscheme and whose comorphisms agree are equal. -/
theorem hom_ext_of_comp_eq_of_app {Z : Scheme.{u}} {i : T ⟶ T'} (hsurj : Function.Surjective i)
    {c d : T' ⟶ Z} (h : i ≫ c = i ≫ d)
    (happ : ∀ (V : Z.Opens) (s : Γ(Z, V)),
      (T'.presheaf.map (eqToHom (preimage_eq_of_comp_eq hsurj h.symm V)).op).hom
        ((c.app V).hom s) = (d.app V).hom s) :
    c = d := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.ext _ _ (base_eq_of_comp_eq hsurj h) ?_
  refine NatTrans.ext (funext fun V => ?_)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  simpa using happ V.unop s

/-- The underlying map of a first-order thickening is surjective. -/
theorem surjective_of_ker_sq_eq_bot {i : T ⟶ T'} [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) :
    Function.Surjective i :=
  (isThickening_of_ker_pow_eq_bot i inferInstance (n := 1) (by simpa using hi)).2

variable {i : T ⟶ T'} {j : Y ⟶ Y'} {a : T ⟶ Y} {a' b' : T' ⟶ Y'}

/-- The two routes around a commutative square have the same preimages, read in the nested
form in which the comorphisms present them. -/
theorem preimage_comp_eq {W Z Z' Z'' : Scheme.{u}} {u : W ⟶ Z} {v : Z ⟶ Z''} {u' : W ⟶ Z'}
    {v' : Z' ⟶ Z''} (e : u ≫ v = u' ≫ v') (V : Z''.Opens) :
    u ⁻¹ᵁ (v ⁻¹ᵁ V) = u' ⁻¹ᵁ (v' ⁻¹ᵁ V) :=
  congrArg (fun p : W ⟶ Z'' => p ⁻¹ᵁ V) e

/-- The square of preimages of a morphism of thickenings. -/
theorem preimage_square (ca : i ≫ a' = a ≫ j) (V : Y'.Opens) :
    i ⁻¹ᵁ (a' ⁻¹ᵁ V) = a ⁻¹ᵁ (j ⁻¹ᵁ V) :=
  preimage_comp_eq ca V

/-- Two restrictions compose to a single one. -/
theorem presheaf_map_map {X : Scheme.{u}} {A B C : (X.Opens)ᵒᵖ}
    (u : A ⟶ B) (v : B ⟶ C) (w : A ⟶ C) (x : X.presheaf.obj A) :
    (X.presheaf.map v).hom ((X.presheaf.map u).hom x) = (X.presheaf.map w).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, presheaf_map_eq _ w]

/-- Three restrictions compose to a single one. -/
theorem presheaf_map_map_map {X : Scheme.{u}} {A B C D : (X.Opens)ᵒᵖ}
    (u : A ⟶ B) (v : B ⟶ C) (t : C ⟶ D) (w : A ⟶ D) (x : X.presheaf.obj A) :
    (X.presheaf.map t).hom ((X.presheaf.map v).hom ((X.presheaf.map u).hom x)) =
      (X.presheaf.map w).hom x := by
  rw [presheaf_map_map u v (u ≫ v), presheaf_map_map (u ≫ v) t w]

/-- A restriction followed by a comorphism is the comorphism followed by a restriction. -/
theorem app_presheaf_map {X Z : Scheme.{u}} (g : X ⟶ Z) {U U' : Z.Opens}
    (u : op U' ⟶ op U) (x : Γ(Z, U')) :
    (g.app U).hom ((Z.presheaf.map u).hom x)
      = (X.presheaf.map ((Opens.map g.base).map u.unop).op).hom ((g.app U').hom x) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]

/-! ### The derivation attached to `θ`, read inside the ambient structure sheaf -/

variable [IsClosedImmersion i]

/-- **The derivation `D = θ ∘ d_{Y/S}` of Equation [Stacks Project, Tag 04BV], read inside the
ambient structure sheaf.** Given a first-order thickening `i : T ⟶ T'`, a morphism `a : T ⟶ Y`
lifting to `a' : T' ⟶ Y'` along `j : Y ⟶ Y'`, and an `𝒪_T`-linear
`θ : a^*Ω_{Y/S} ⟶ 𝒞_{T/T'}`, this is the value of `D` on a section `y` of `𝒪_Y` over
`j⁻¹V`, viewed as a section of the defining ideal of `i` inside `𝒪_{T'}` over `a'⁻¹V`.

It is `θ` transposed along `a^* ⊣ a_*`, applied to the universal derivation of `y`, and then
included into `𝒪_{T'}` by `Stacks.Thickenings.firstOrderImmersionConormalSheafι`. -/
def derivationSectionι (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
    (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i)
    (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) : Γ(T', a' ⁻¹ᵁ V) :=
  ((firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ V)))
    ((Stacks.Conormal.conormalSheaf i).val.map (eqToHom (preimage_square ca V)).op
      ((((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
            (Scheme.Hom.relativeDifferentials (j ≫ q))
            (Stacks.Conormal.conormalSheaf i) θ).val.app (op (j ⁻¹ᵁ V)))
        ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d y)))

/-! ### The conormal sections of a morphism of thickenings, inside the ambient sheaf -/

/-- **A conormal section of `i` over `a⁻¹j⁻¹V`, read inside `𝒪_{T'}` over `a'⁻¹V`.** The square
`i ≫ a' = a ≫ j` identifies `i⁻¹(a'⁻¹V)` with `a⁻¹(j⁻¹V)`, so a section of `𝒞_{T/T'}` over the
latter is a section of `i_* 𝒞_{T/T'}` over `a'⁻¹V`; this is its image under
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`.

It is the outer half of `Stacks.Thickenings.derivationSectionι`, isolated so that its additivity,
its semilinearity along `(a')^♯` and its naturality in `V` are stated once. -/
def conormalSectionι (hi : i.ker ^ 2 = ⊥) (ca : i ≫ a' = a ≫ j) (V : Y'.Opens)
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    Γ(T', a' ⁻¹ᵁ V) :=
  (firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ V))
    ((Stacks.Conormal.conormalSheaf i).val.map (eqToHom (preimage_square ca V)).op m)

section ConormalSectionι

variable (hi : i.ker ^ 2 = ⊥) (ca : i ≫ a' = a ≫ j)

/-- **`Stacks.Thickenings.conormalSectionι` as an additive map.** It is the composite of two
additive maps, the restriction of `𝒞_{T/T'}` along the square and the inclusion
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`. -/
def conormalSectionιHom (V : Y'.Opens) :
    (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V))) →+ Γ(T', a' ⁻¹ᵁ V) :=
  ((firstOrderImmersionConormalSheafι i hi).val.app
      (op (a' ⁻¹ᵁ V))).hom.toAddMonoidHom.comp
    ((Stacks.Conormal.conormalSheaf i).val.map
      (eqToHom (preimage_square ca V)).op).hom.toAddMonoidHom

/-- `Stacks.Thickenings.conormalSectionιHom` is `Stacks.Thickenings.conormalSectionι`. -/
theorem conormalSectionιHom_apply (V : Y'.Opens)
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    conormalSectionιHom hi ca V m = conormalSectionι hi ca V m := rfl

/-- `Stacks.Thickenings.conormalSectionι` is additive. -/
theorem conormalSectionι_add (V : Y'.Opens)
    (m n : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    conormalSectionι hi ca V (m + n) =
      conormalSectionι hi ca V m + conormalSectionι hi ca V n :=
  map_add (conormalSectionιHom hi ca V) m n

omit [IsClosedImmersion i] in
/-- **The two routes around the square `i ≫ a' = a ≫ j`, on sections over `V`.** The image of a
section of `𝒪_{Y'}` under `(a')^♯` and then `i^♯` is its image under `j^♯` and then `a^♯`, read
across the identification of `i⁻¹a'⁻¹V` with `a⁻¹j⁻¹V`. -/
theorem app_square_eq (V : Y'.Opens) (s : Γ(Y', V)) :
    (T.presheaf.map (eqToHom (preimage_square ca V)).op).hom
        ((a.app (j ⁻¹ᵁ V)).hom ((j.app V).hom s)) =
      (i.app (a' ⁻¹ᵁ V)).hom ((a'.app V).hom s) := by
  have h := Scheme.Hom.congr_app ca V
  have h2 := congrArg
    (fun φ : Γ(Y', V) ⟶ Γ(T, i ⁻¹ᵁ (a' ⁻¹ᵁ V)) ↦ φ.hom s) h
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply] at h2
  exact h2.symm

/-- **`Stacks.Thickenings.conormalSectionι` carries a scalar out as a factor.** If a section `c`
of `𝒪_T` over `a⁻¹j⁻¹V` restricts to the image under `i^♯` of a section `ρ` of `𝒪_{T'}` over
`a'⁻¹V`, then scaling by `c` becomes multiplication by `ρ`.

Both halves are `map_smul`: that of the restriction map of `𝒞_{T/T'}` and that of
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`, whose scalars over `a'⁻¹V` are those of
`𝒪_{T'}` acting through `i^♯`. -/
theorem conormalSectionι_smul (V : Y'.Opens) (ρ : Γ(T', a' ⁻¹ᵁ V))
    (c : Γ(T, a ⁻¹ᵁ (j ⁻¹ᵁ V)))
    (hc : (T.presheaf.map (eqToHom (preimage_square ca V)).op).hom c =
      (i.app (a' ⁻¹ᵁ V)).hom ρ)
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    conormalSectionι hi ca V (c • m) = ρ * conormalSectionι hi ca V m := by
  have h1 : (Stacks.Conormal.conormalSheaf i).val.map
        (eqToHom (preimage_square ca V)).op (c • m) =
      (T.presheaf.map (eqToHom (preimage_square ca V)).op).hom c •
        (Stacks.Conormal.conormalSheaf i).val.map (eqToHom (preimage_square ca V)).op m :=
    PresheafOfModules.map_smul _ _ _ _
  change (firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ V))
      ((Stacks.Conormal.conormalSheaf i).val.map
        (eqToHom (preimage_square ca V)).op (c • m)) = _
  rw [h1, hc]
  exact app_firstOrderImmersionConormalSheafι_smul i hi (a' ⁻¹ᵁ V) ρ _

/-- **`Stacks.Thickenings.conormalSectionι` is natural in `V`.** Restricting a conormal section
to a smaller open and then including it into `𝒪_{T'}` is including it and then restricting.

The restriction maps of `𝒞_{T/T'}` compose to a single one, the category of opens being thin,
and `Stacks.Thickenings.firstOrderImmersionConormalSheafι` is a morphism of sheaves. -/
theorem conormalSectionι_naturality {V W : Y'.Opens} (hWV : W ≤ V)
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))) :
    conormalSectionι hi ca W
        ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE (a.preimage_mono (j.preimage_mono hWV))).op m) =
      (T'.presheaf.map (homOfLE (a'.preimage_mono hWV)).op).hom
        (conormalSectionι hi ca V m) := by
  have hnat : (firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ W))
        ((Stacks.Conormal.conormalSheaf i).val.map
          (homOfLE (i.preimage_mono (a'.preimage_mono hWV))).op
          ((Stacks.Conormal.conormalSheaf i).val.map
            (eqToHom (preimage_square ca V)).op m)) =
      (T'.presheaf.map (homOfLE (a'.preimage_mono hWV)).op).hom
        ((firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ V))
          ((Stacks.Conormal.conormalSheaf i).val.map
            (eqToHom (preimage_square ca V)).op m)) :=
    PresheafOfModules.naturality_apply (firstOrderImmersionConormalSheafι i hi).val
      (homOfLE (a'.preimage_mono hWV)).op _
  refine Eq.trans ?_ hnat
  have hle : i ⁻¹ᵁ (a' ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (j ⁻¹ᵁ V) :=
    (preimage_square ca W).le.trans (a.preimage_mono (j.preimage_mono hWV))
  exact congrArg
    (fun n ↦ (firstOrderImmersionConormalSheafι i hi).val.app (op (a' ⁻¹ᵁ W)) n)
    ((module_map_map (homOfLE (a.preimage_mono (j.preimage_mono hWV))).op
          (eqToHom (preimage_square ca W)).op (homOfLE hle).op m).trans
      (module_map_map (eqToHom (preimage_square ca V)).op
        (homOfLE (i.preimage_mono (a'.preimage_mono hWV))).op (homOfLE hle).op m).symm)

end ConormalSectionι

section Properties

variable (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
  (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
    Stacks.Conormal.conormalSheaf i)

/-- **`Stacks.Thickenings.derivationSectionι` as an additive map.** All three maps it is built
from are additive — the universal derivation, the transposed `θ` and the inclusion of the
conormal sheaf — so it is the composite of three `AddMonoidHom`s.

Bundling it is what makes `Mathlib`'s `map_add` and `map_zero` applicable: the intermediate
objects carry two definitionally equal but syntactically distinct additions, one from each
spelling of the module they live in, and a rewrite cannot cross that junction. -/
def derivationSectionιHom (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
    (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i)
    (V : Y'.Opens) : Γ(Y, j ⁻¹ᵁ V) →+ Γ(T', a' ⁻¹ᵁ V) :=
  (((firstOrderImmersionConormalSheafι i hi).val.app
          (op (a' ⁻¹ᵁ V))).hom.toAddMonoidHom.comp
      ((Stacks.Conormal.conormalSheaf i).val.map
        (eqToHom (preimage_square ca V)).op).hom.toAddMonoidHom).comp
    ((((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
            (Scheme.Hom.relativeDifferentials (j ≫ q))
            (Stacks.Conormal.conormalSheaf i) θ).val.app
          (op (j ⁻¹ᵁ V))).hom.toAddMonoidHom.comp
      (Scheme.Hom.universalRelativeDerivation (j ≫ q)).d)

/-- `Stacks.Thickenings.derivationSectionιHom` is `Stacks.Thickenings.derivationSectionι`. -/
theorem derivationSectionιHom_apply (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionιHom hi q ca θ V y = derivationSectionι hi q ca θ V y := rfl

/-- `Stacks.Thickenings.derivationSectionι` is additive in the section it differentiates: all
three maps it is built from are. -/
theorem derivationSectionι_add (V : Y'.Opens) (y z : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca θ V (y + z) =
      derivationSectionι hi q ca θ V y + derivationSectionι hi q ca θ V z :=
  map_add (derivationSectionιHom hi q ca θ V) y z

/-- `Stacks.Thickenings.derivationSectionι` kills `0`. -/
theorem derivationSectionι_zero (V : Y'.Opens) : derivationSectionι hi q ca θ V 0 = 0 :=
  map_zero (derivationSectionιHom hi q ca θ V)

/-- **The outer half of `Stacks.Thickenings.derivationSectionι` as an additive map**, from the
sections of `Ω_{Y/S}` over `j⁻¹V`: the transposed `θ` followed by
`Stacks.Thickenings.conormalSectionι`. -/
def derivationSectionιOuter (V : Y'.Opens) :
    (Scheme.Hom.relativeDifferentials (j ≫ q)).val.obj (op (j ⁻¹ᵁ V)) →+
      Γ(T', a' ⁻¹ᵁ V) :=
  (conormalSectionιHom hi ca V).comp
    ((((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Scheme.Hom.relativeDifferentials (j ≫ q))
        (Stacks.Conormal.conormalSheaf i) θ).val.app (op (j ⁻¹ᵁ V))).hom.toAddMonoidHom)

/-- `Stacks.Thickenings.derivationSectionι` is `Stacks.Thickenings.derivationSectionιOuter`
applied to the universal derivation. -/
theorem derivationSectionι_eq_outer (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca θ V y =
      derivationSectionιOuter hi q ca θ V
        ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d y) :=
  rfl

/-- **`Stacks.Thickenings.derivationSectionι` vanishes where the universal derivation does.** -/
theorem derivationSectionι_eq_zero_of_d_eq_zero (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V))
    (hy : (Scheme.Hom.universalRelativeDerivation (j ≫ q)).d y = 0) :
    derivationSectionι hi q ca θ V y = 0 :=
  (derivationSectionι_eq_outer hi q ca θ V y).trans
    ((congrArg (derivationSectionιOuter hi q ca θ V) hy).trans (map_zero _))

/-- **`Stacks.Thickenings.derivationSectionι` kills the sections coming from the base.** For a
section `r` of `𝒪_S` over `W`, the derivation `D` vanishes on `(j ≫ q)^♯ r`, because the
universal relative derivation does. -/
theorem derivationSectionι_app_comp_eq_zero (W : S.Opens) (r : Γ(S, W)) :
    derivationSectionι hi q ca θ (q ⁻¹ᵁ W) (((j ≫ q).app W).hom r) = 0 :=
  derivationSectionι_eq_zero_of_d_eq_zero hi q ca θ (q ⁻¹ᵁ W) _
    (Scheme.Hom.universalRelativeDerivation_d_app_eq_zero (j ≫ q) W r)

/-- **`Stacks.Thickenings.derivationSectionι` split at the conormal sheaf.** It is the transposed
`θ` applied to the universal derivation, followed by
`Stacks.Thickenings.conormalSectionι`. -/
theorem derivationSectionι_eq (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca θ V y =
      conormalSectionι hi ca V
        ((((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
              (Scheme.Hom.relativeDifferentials (j ≫ q))
              (Stacks.Conormal.conormalSheaf i) θ).val.app (op (j ⁻¹ᵁ V)))
          ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).d y)) :=
  rfl

/-- **`Stacks.Thickenings.derivationSectionι` takes values in the defining ideal of `i`.** It is
read inside `𝒪_{T'}` through `Stacks.Thickenings.firstOrderImmersionConormalSheafι`, which
factors through the inclusion of that ideal. -/
theorem app_derivationSectionι_eq_zero (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    (i.app (a' ⁻¹ᵁ V)).hom (derivationSectionι hi q ca θ V y) = 0 :=
  app_firstOrderImmersionConormalSheafι_eq_zero i hi (a' ⁻¹ᵁ V) _

/-- Scaling a conormal section that reads as `D y` by `j^♯ s` multiplies `D y` by `(a')^♯ s`. -/
private theorem conormalSectionι_smul_of_eq_derivationSectionι (V : Y'.Opens) (s : Γ(Y', V))
    (y : Γ(Y, j ⁻¹ᵁ V))
    (m : (Stacks.Conormal.conormalSheaf i).val.obj (op (a ⁻¹ᵁ (j ⁻¹ᵁ V))))
    (hm : conormalSectionι hi ca V m = derivationSectionι hi q ca θ V y) :
    conormalSectionι hi ca V ((a.app (j ⁻¹ᵁ V)).hom ((j.app V).hom s) • m) =
      (a'.app V).hom s * derivationSectionι hi q ca θ V y :=
  (conormalSectionι_smul hi ca V _ _ (app_square_eq ca V s) m).trans (congrArg _ hm)

/-- **The Leibniz rule for `Stacks.Thickenings.derivationSectionι` along `(a')^♯`.** On sections
`s`, `t` of `𝒪_{Y'}` over `V`, pulled back to `𝒪_Y` by `j^♯`, the derivation `D` satisfies
`D(st) = (a')^♯(s) · D(t) + (a')^♯(t) · D(s)`.

The universal derivation satisfies the Leibniz rule with the scalar action of `𝒪_Y`; the
transposed `θ` is `𝒪_Y`-linear; and `Stacks.Thickenings.conormalSectionι` turns the scalar
`j^♯ s` into the factor `(a')^♯ s` by `Stacks.Thickenings.conormalSectionι_smul`, the square
`i ≫ a' = a ≫ j` being what matches the two. -/
theorem derivationSectionι_leibniz (V : Y'.Opens) (s t : Γ(Y', V)) :
    derivationSectionι hi q ca θ V ((j.app V).hom (s * t)) =
      (a'.app V).hom s * derivationSectionι hi q ca θ V ((j.app V).hom t) +
        (a'.app V).hom t * derivationSectionι hi q ca θ V ((j.app V).hom s) := by
  have hD := ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp
      (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Scheme.Hom.relativeDifferentials (j ≫ q))
        (Stacks.Conormal.conormalSheaf i) θ).val)).d_mul
    (X := op (j ⁻¹ᵁ V)) ((j.app V).hom s) ((j.app V).hom t)
  rw [map_mul, derivationSectionι_eq]
  refine (congrArg (conormalSectionι hi ca V) hD).trans ?_
  exact (conormalSectionι_add hi ca V _ _).trans
    (congrArg₂ (· + ·)
      (conormalSectionι_smul_of_eq_derivationSectionι hi q ca θ V s _ _
        (derivationSectionι_eq hi q ca θ V _).symm)
      (conormalSectionι_smul_of_eq_derivationSectionι hi q ca θ V t _ _
        (derivationSectionι_eq hi q ca θ V _).symm))

/-- **`Stacks.Thickenings.derivationSectionι` is natural in `V`.** Differentiating a section and
restricting to a smaller open is restricting and then differentiating: the universal derivation
commutes with restriction, the transposed `θ` is a morphism of sheaves, and
`Stacks.Thickenings.conormalSectionι` is natural by
`Stacks.Thickenings.conormalSectionι_naturality`. -/
theorem derivationSectionι_naturality {V W : Y'.Opens} (hWV : W ≤ V) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca θ W
        ((Y.presheaf.map (homOfLE (j.preimage_mono hWV)).op).hom y) =
      (T'.presheaf.map (homOfLE (a'.preimage_mono hWV)).op).hom
        (derivationSectionι hi q ca θ V y) := by
  have hD := ((Scheme.Hom.universalRelativeDerivation (j ≫ q)).postcomp
      (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Scheme.Hom.relativeDifferentials (j ≫ q))
        (Stacks.Conormal.conormalSheaf i) θ).val)).d_map
    (homOfLE (j.preimage_mono hWV)).op y
  rw [derivationSectionι_eq]
  exact (congrArg (conormalSectionι hi ca W) hD).trans (conormalSectionι_naturality hi ca hWV _)

/-- **Two values of `Stacks.Thickenings.derivationSectionι` multiply to zero**: both lie in the
defining ideal of the first-order thickening `i`, which is square-zero. -/
theorem derivationSectionι_mul_derivationSectionι (V : Y'.Opens) (y z : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca θ V y * derivationSectionι hi q ca θ V z = 0 := by
  have hm : derivationSectionι hi q ca θ V y * derivationSectionι hi q ca θ V z ∈
      RingHom.ker (i.app (a' ⁻¹ᵁ V)).hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (app_derivationSectionι_eq_zero hi q ca θ V y)
      (app_derivationSectionι_eq_zero hi q ca θ V z)
  rw [ker_app_sq_eq_bot i hi (a' ⁻¹ᵁ V)] at hm
  exact Ideal.mem_bot.mp hm

end Properties

/-! ### The action of `θ` on a lift, at sheaf level -/

/-- **`b'` is the lift `θ ⬝ a'` of [Stacks Project, Tag 0CK1].** For a first-order thickening
`i : T ⟶ T'` and two lifts `a'`, `b'` of the same `a : T ⟶ Y` along `j : Y ⟶ Y'`, this says
that the comorphism of `b'` is the comorphism of `a'` plus the derivation
`D = θ ∘ d_{Y/S}` of Equation [Stacks Project, Tag 04BV], precomposed with `j^♯`. That is
exactly the condition that the difference derivation of [Stacks Project, Tag 04FG] for the pair
`(b', a')` is `D`, which by [Stacks Project, Tag 02H5] determines `b'` uniquely. -/
def IsDerivationAction (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
    (cb : i ≫ b' = a ≫ j)
    (θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i) : Prop :=
  ∀ (V : Y'.Opens) (s : Γ(Y', V)),
    (T'.presheaf.map
        (eqToHom (preimage_eq_of_comp_eq (surjective_of_ker_sq_eq_bot hi)
          (cb.trans ca.symm) V)).op).hom
        ((a'.app V).hom s + derivationSectionι hi q ca θ V ((j.app V).hom s))
      = (b'.app V).hom s

/-- **At most one morphism is `θ ⬝ a'`**, the uniqueness half of [Stacks Project, Tag 02H5] at
sheaf level. Two lifts of `a` whose comorphisms are both `(a')^♯ + D` agree. -/
theorem eq_of_isDerivationAction (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (ca : i ≫ a' = a ≫ j)
    {c d : T' ⟶ Y'} (cc : i ≫ c = a ≫ j) (cd : i ≫ d = a ≫ j)
    {θ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i}
    (hc : IsDerivationAction hi q ca cc θ) (hd : IsDerivationAction hi q ca cd θ) : c = d := by
  refine hom_ext_of_comp_eq_of_app (surjective_of_ker_sq_eq_bot hi)
    (cc.trans cd.symm) fun V s => ?_
  rw [← hc V s, ← hd V s]
  exact presheaf_map_map _ _ _ _

/-! ### The compatibility of the actions -/

section Comm

variable {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u}}
  {i₁ : T₁ ⟶ T₁'} {i₂ : T₂ ⟶ T₂'} {j₁ : X₁ ⟶ X₁'} {j₂ : X₂ ⟶ X₂'}
  {a₁ : T₁ ⟶ X₁} {a₁' b₁' : T₁' ⟶ X₁'} {a₂ : T₂ ⟶ X₂} {a₂' b₂' : T₂' ⟶ X₂'}
  {h : T₂ ⟶ T₁} {h' : T₂' ⟶ T₁'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂]

/-- **Acting by compatible derivation data commutes with the vertical maps**, the form of
[Stacks Project, Tag 04BZ] for arbitrary schemes in which the two lifts are morphisms assumed to
satisfy the comorphism equation. Let `(h, h')` and `(f, f')` be the vertical
maps of a diagram of first-order thickenings as in [Stacks Project, Tag 04BY], let `(a₁, a₁')`
and `(a₂, a₂')` be morphisms of thickenings compatible with them, and let `p₁ : X₁' ⟶ S₁` and
`p₂ : X₂' ⟶ S₂` be the structure morphisms. Nothing is assumed étale and nothing is assumed
affine. Given `θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` and `θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` whose
derivations `D_n = θ_n ∘ d_{X_n/S_n}` of Equation [Stacks Project, Tag 04BV] satisfy
`D₂ (f^♯ y) = (h')^♯ (D₁ y)` — the commuting square of the source, read inside the ambient
structure sheaves — the lifts `b₁' = θ₁ ⬝ a₁'` and `b₂' = θ₂ ⬝ a₂'` of
[Stacks Project, Tag 0CK1] give a commutative square:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```

Both sides restrict to `(a₂ ≫ f) ≫ j₁ = (h ≫ a₁) ≫ j₁` on `T₂`, so they have the same
underlying map; their comorphisms are compared section by section, where the terms coming from
the lifts `a₁'`, `a₂'` agree because `a₂' ≫ f' = h' ≫ a₁'` and the terms coming from the data
agree by the hypothesis `hθ`. The section `s` of `𝒪_{X₁'}` over `V` enters `hθ` through
`y = j₁^♯ s`, and `j₂^♯ (f')^♯ s = f^♯ j₁^♯ s` because `j₂ ≫ f' = f ≫ j₁`; so `hθ` is the
source's square for the sections of `𝒪_{X₁}` that come from the ambient scheme.

The two lifts enter here as morphisms `b₁'`, `b₂'` *assumed* to satisfy
`Stacks.Thickenings.IsDerivationAction`, so the remark itself is not registered on this
statement; it is registered on
`Stacks.Thickenings.derivationActionSheaf_comp_of_derivationSection_comm`, which is this
statement with both lifts the constructed `Stacks.Thickenings.derivationActionSheaf` and is
proved from it by discharging the two assumptions with
`Stacks.Thickenings.isDerivationAction_derivationActionSheaf`. -/
theorem derivationAction_comp_of_derivationSection_comm
    (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (p₁ : X₁' ⟶ S₁) (p₂ : X₂' ⟶ S₂)
    (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁) (cb₁ : i₁ ≫ b₁' = a₁ ≫ j₁)
    (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂) (cb₂ : i₂ ≫ b₂' = a₂ ≫ j₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cj : j₂ ≫ f' = f ≫ j₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cA : a₂' ≫ f' = h' ≫ a₁')
    {θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁}
    {θ₂ : (Scheme.Modules.pullback a₂).obj (Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)) ⟶
      Stacks.Conormal.conormalSheaf i₂}
    (hb₁ : IsDerivationAction hi₁ p₁ ca₁ cb₁ θ₁)
    (hb₂ : IsDerivationAction hi₂ p₂ ca₂ cb₂ θ₂)
    (hθ : ∀ (V : X₁'.Opens) (s : Γ(X₁', V)),
      (T₂'.presheaf.map (eqToHom (preimage_comp_eq cA V)).op).hom
          ((h'.app (a₁' ⁻¹ᵁ V)).hom (derivationSectionι hi₁ p₁ ca₁ θ₁ V ((j₁.app V).hom s)))
        = derivationSectionι hi₂ p₂ ca₂ θ₂ (f' ⁻¹ᵁ V)
            ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s))) :
    b₂' ≫ f' = h' ≫ b₁' := by
  have hcomp : i₂ ≫ (b₂' ≫ f') = i₂ ≫ (h' ≫ b₁') := by
    rw [reassoc_of% cb₂, reassoc_of% cT, cj, reassoc_of% cX, cb₁]
  refine hom_ext_of_comp_eq_of_app (surjective_of_ker_sq_eq_bot hi₂) hcomp fun V s => ?_
  have e₂ := hb₂ (f' ⁻¹ᵁ V) ((f'.app V).hom s)
  have e₁ := hb₁ V s
  have hA : (a₂'.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s) =
      (T₂'.presheaf.map (eqToHom (preimage_comp_eq cA V)).op).hom
        ((h'.app (a₁' ⁻¹ᵁ V)).hom ((a₁'.app V).hom s)) := by
    have := Scheme.Hom.congr_app cA V
    rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at this
    exact congrArg (fun φ : Γ(X₁', V) ⟶ _ => φ.hom s) this
  have g₂ : ((b₂' ≫ f').app V).hom s = _ := e₂.symm
  have g₁ : ((h' ≫ b₁').app V).hom s
      = (h'.app (b₁' ⁻¹ᵁ V)).hom ((b₁'.app V).hom s) := rfl
  rw [g₂, g₁, ← e₁, app_presheaf_map, hA, ← hθ V s, ← map_add, ← map_add]
  exact presheaf_map_map_map _ _ _ _ _

end Comm

end Stacks.Thickenings

end
