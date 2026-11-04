module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# Inverse image of sheaves of modules transposes derivations

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi, `a : A ⟶ P` a morphism of sheaves of
commutative rings on `D` and `M` a sheaf of modules over the inverse image of `P`. This file
proves that the adjunction `f⁻¹ ⊣ f_*` of Stacks 03D3 for sheaves of modules carries
derivations to derivations both ways:
`Der_{f⁻¹A}(f⁻¹P, M) = Der_A(P, f_*M)`.

A derivation in the sense of `PresheafOfModules.Derivation'` is a *pointwise* datum: an
additive map on sections over each object of the site, subject to the Leibniz rule on
sections. The inverse image along a morphism of topoi is not pointwise — there is no
description of the sections of `f⁻¹`. So the derivation axioms are first rewritten as
commuting squares of morphisms of sheaves of *sets* (`IsDerivationHom`), and those squares are
then transported across the hom-set bijection of `f⁻¹ ⊣ f_*` using that `f⁻¹` is left exact,
so that its binary-product comparison is invertible.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.leibnizHom` is the right-hand side of the Leibniz rule
  for a candidate derivation, as a morphism of sheaves of sets out of `O ⨯ O`.
* `Stacks.Sheaves.RingedToposModules.derivationSheafHom` is the morphism of underlying sheaves
  of sets belonging to a derivation, and
  `Stacks.Sheaves.RingedToposModules.IsDerivationHom` is the diagrammatic form of the
  derivation axioms for such a morphism.
* `PresheafOfModules.Derivation'.precomp` is the precomposition of a derivation by a morphism
  of presheaves of commutative rings under the base, the counterpart of Mathlib's
  `PresheafOfModules.Derivation.postcomp`.
* `Stacks.Sheaves.RingedToposModules.inverseImageDifferentials` is the inverse image
  `f⁻¹Ω_{P/A}` of the sheaf of relative differentials, and
  `Stacks.Sheaves.RingedToposModules.inverseImageDifferentialsCorepresentableBy` is its
  universal property.

## Main results

* `Stacks.Sheaves.RingedToposModules.derivationHomEquiv`: a derivation of a sheaf of modules
  over a morphism of sheaves of commutative rings on a site is the same thing as a morphism of
  the underlying sheaves of sets satisfying `IsDerivationHom`.
* `Stacks.Sheaves.RingedToposModules.homEquiv_ringAddHom_iff`,
  `homEquiv_ringMulHom_iff` and `homEquiv_constant_iff`: each of the three derivation axioms
  holds for a morphism out of an inverse image exactly when it holds for its adjunct.
* `Stacks.Sheaves.RingedToposModules.isDerivationHom_transpose_iff` and
  `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv`: the transposition itself.
* `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv_postcomp`: the transposition
  is natural in the coefficient module.
* `Stacks.Sheaves.RingedToposModules.derivationSheafHom_inverseImageDerivationEquiv_precomp`
  and `Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv_precomp_d`: it is natural
  in the sheaf of commutative rings, stated on the underlying morphisms of sheaves of sets and
  on sections, the two coefficient modules not being definitionally equal.
* `Stacks.Sheaves.RingedToposModules.inverseImageDifferentialsIso` and
  `Stacks.Sheaves.RingedToposModules.homEquiv_inverseImageDifferentialsIso_hom`: the inverse
  image of the sheaf of relative differentials is the sheaf of relative differentials of the
  inverse image, `f⁻¹Ω_{P/A} ≅ Ω_{f⁻¹P/f⁻¹A}`, by the unique identification carrying one
  universal derivation to the other.

## Implementation notes

The three axioms are transported one at a time. Additivity is a square built from one binary
operation on each side, so it goes through `homEquiv_binary_iff`, exactly as linearity of a
morphism of sheaves of modules does in
`Stacks.Sheaves.RingedToposModules.homEquiv_moduleAddHom_iff`. The Leibniz rule is not of that
shape: its right-hand side is a composite of two scalar multiplications and one addition, so it
is transported by `homEquiv_prodComparison_leibniz`, a lemma about an arbitrary adjunction and
an arbitrary pair of a "scalar multiplication" and an "addition", built from `homEquiv_prodLift`
(the adjunct of a morphism into a binary product). The scalars on the direct-image side act
through the unit `O ⟶ f_*f⁻¹O`, by `prodLift_moduleSMulHom_directImageModules`, and the adjunct
of `f⁻¹` of a morphism into the ring sheaf is that morphism followed by the unit
(`homEquiv_inverseImage_map_ringUnit`); together these make the two Leibniz diagrams match.

Several steps are term-mode `Eq.trans`/`congrArg` chains rather than `rw`. The underlying sheaf
of sets of `f⁻¹O` *is* `f⁻¹` of the underlying sheaf of sets of `O`, but the two spellings are
definitionally and not syntactically equal, and a motive mentioning both is not type-correct at
the transparency `rw` uses; term-mode elaboration is at default transparency and accepts them.

Vanishing on the image of `a` is stated as the assertion that the composite `O₁ ⟶ M` is
*constant*, in the form `prod.fst ≫ a ≫ d = prod.snd ≫ a ≫ d` on `O₁ ⨯ O₁`. Together with
additivity this is equivalent to vanishing (`isDerivationHom_base_apply`), and in this form no
zero section and no terminal object enter, so the condition transports by naturality of the
hom-set bijection alone (`homEquiv_constant_iff`).

The coefficient module `M` is arbitrary among the sheaves of modules over the inverse image of
`P`. In particular the statement covers the case of a module whose scalars have been restricted
along a further morphism `c : P' ⟶ P` of sheaves of commutative rings, which is the shape in
which the cotangent complex of `CategoryTheory.Sheaf.cotangentComplex` takes its derivations:
instantiate `A`, `P` at the two rings of the derivation and `M` at the restricted module.

The two sites, their morphism universes and the two universes of sections all vary
independently, as in `Stacks.Sheaves.RingedToposModules.toposModulesHomEquiv`.

Tag 08TQ follows from the transposition together with its naturality in the coefficient module:
`Ω_{P/A}` corepresents the `A`-derivations of `P`, so its inverse image corepresents the
`A`-derivations with values in a direct image, which are the `f⁻¹A`-derivations of `f⁻¹P`, and
two corepresenting objects of one functor are isomorphic. That is
`inverseImageDifferentialsIso`. Nothing about the sections of `f⁻¹` enters, and the generality
is that of the transposition: an arbitrary morphism of topoi, with the object, arrow and section
universes of the two sites independent.

### No `@[stacks 08SV]`

Tag 08SV is the same statement for the cotangent complex, and it is not claimed here. Beyond
08TQ it needs the comparison of the two standard resolutions
(`StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolutionComparison`) carried
through the base change of the sheaves of differentials along the augmentations, which needs one
statement that is not in this development: that the direct image of a sheaf of modules commutes
with restriction of scalars along a morphism of sheaves of commutative rings on the target. The
two `P'`-module structures on `f_*M`, one obtained by restricting along `c : P' ⟶ P` and then
pushing forward, the other by pushing forward and restricting along the unit, agree by
naturality of the unit `P' ⟶ f_*f⁻¹P'`, but that identification is not definitional.

## References

* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf

namespace PresheafOfModules.Derivation'

universe v u v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] {S R₁ R₂ : Dᵒᵖ ⥤ CommRingCat.{u}}
  {a₁ : S ⟶ R₁} {a₂ : S ⟶ R₂} (q : R₁ ⟶ R₂)
  {M : PresheafOfModules.{v} (R₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- Precomposition of a derivation by a morphism `q : R₁ ⟶ R₂` of presheaves of commutative
rings under `S`: an `R₂/S`-derivation with values in `M` is an `R₁/S`-derivation with values in
`M` viewed as a presheaf of `R₁`-modules by restriction of scalars along `q`. -/
noncomputable def precomp (d : M.Derivation' a₂) (h : a₁ ≫ q = a₂) :
    ((restrictScalars (whiskerRight q (forget₂ CommRingCat.{u} RingCat.{u}))).obj
      M).Derivation' a₁ where
  d {X} := d.d.comp (q.app X).hom.toAddMonoidHom
  d_mul {X} x y := by
    change d.d ((q.app X).hom (x * y)) = _
    rw [map_mul]
    exact d.d_mul _ _
  d_map {X Y} g x := by
    change d.d ((q.app Y).hom ((R₁.map g).hom x)) = M.map g (d.d ((q.app X).hom x))
    rw [← d.d_map g ((q.app X).hom x)]
    exact congrArg d.d (ConcreteCategory.congr_hom (q.naturality g) x)
  d_app {X} s := by
    subst h
    exact d.d_app s

/-- The precomposed derivation `d.precomp q h` sends a section `x` to `d` of its image
under `q`. -/
@[simp]
lemma precomp_d_apply (d : M.Derivation' a₂) (h : a₁ ≫ q = a₂) {X : Dᵒᵖ} (x : R₁.obj X) :
    (d.precomp q h).d x = d.d ((q.app X).hom x) :=
  rfl

end PresheafOfModules.Derivation'

namespace Stacks.Sheaves.RingedToposModules

/-! ## The Leibniz diagram -/

section Leibniz

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (M : SheafOfModules.{w} R)

/-- The right-hand side of the Leibniz rule for a candidate derivation `d`, as a morphism of
sheaves of sets `R ⨯ R ⟶ M`: on sections it is `(x, y) ↦ x • d y + y • d x`. -/
noncomputable def leibnizHom (d : Sheaf.ringSheaf R ⟶ Sheaf.moduleSheaf R M) :
    Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶ Sheaf.moduleSheaf R M :=
  prod.lift (prod.lift prod.fst (prod.snd ≫ d) ≫ Sheaf.moduleSMulHom R M)
      (prod.lift prod.snd (prod.fst ≫ d) ≫ Sheaf.moduleSMulHom R M) ≫
    Sheaf.moduleAddHom R M

/-- `leibnizHom`, unfolded. A rewriting handle: `leibnizHom` is a `def`, so that the
`sectionsFunctor` computation rule below is not unfolded by `dsimp`. -/
lemma leibnizHom_eq (d : Sheaf.ringSheaf R ⟶ Sheaf.moduleSheaf R M) :
    leibnizHom R M d =
      prod.lift (prod.lift prod.fst (prod.snd ≫ d) ≫ Sheaf.moduleSMulHom R M)
          (prod.lift prod.snd (prod.fst ≫ d) ≫ Sheaf.moduleSMulHom R M) ≫
        Sheaf.moduleAddHom R M :=
  rfl

/-- On sections, `leibnizHom R M d` sends a pair `(x, y)` to `x • d y + y • d x`. -/
@[simp]
lemma sectionsFunctor_map_leibnizHom (d : Sheaf.ringSheaf R ⟶ Sheaf.moduleSheaf R M) (X : Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R)) :
    (Sheaf.sectionsFunctor J X).map (leibnizHom R M d)
        (prodObjMk (A := Sheaf.ringSheaf R) (B := Sheaf.ringSheaf R) x y) =
      x • (Sheaf.sectionsFunctor J X).map d y + y • (Sheaf.sectionsFunctor J X).map d x := by
  rw [leibnizHom, (Sheaf.sectionsFunctor J X).map_comp_apply, map_lift_apply,
    (Sheaf.sectionsFunctor J X).map_comp_apply, (Sheaf.sectionsFunctor J X).map_comp_apply,
    map_lift_apply, map_lift_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    (Sheaf.sectionsFunctor J X).map_comp_apply, (Sheaf.sectionsFunctor J X).map_comp_apply,
    map_fst_prodObjMk, map_snd_prodObjMk, Sheaf.sectionsFunctor_map_moduleSMulHom,
    Sheaf.sectionsFunctor_map_moduleSMulHom, Sheaf.sectionsFunctor_map_moduleAddHom]

end Leibniz

/-! ## Derivations as morphisms of the underlying sheaves of sets -/

section DerivationHom

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (a : O₁ ⟶ O₂)
  (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂))

/-- The morphism of underlying sheaves of sets of a morphism of sheaves of commutative
rings. -/
noncomputable abbrev commRingSetHom :
    Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⟶
      Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) :=
  (sheafCompose J (forget RingCat.{w})).map ((Stacks.forgetCommRingSheaf.{v, u, w} J).map a)

/-- The morphism of underlying sheaves of sets belonging to a derivation. -/
noncomputable def derivationSheafHom (d : M.val.Derivation' a.hom) :
    Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M :=
  Sheaf.unaryOpHom (fun _ x ↦ d.d x) fun g x ↦ (d.d_map g x).symm

/-- On sections, `derivationSheafHom a M d` acts as the derivation `d`. -/
@[simp]
lemma sectionsFunctor_map_derivationSheafHom (d : M.val.Derivation' a.hom) (X : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J X).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂))) :
    (Sheaf.sectionsFunctor J X).map (derivationSheafHom a M d) x = d.d x := rfl

/-- Being a derivation over `a`, stated diagrammatically for a morphism of the underlying
sheaves of sets `O₂ ⟶ M`: additivity, the Leibniz rule, and constancy along the image of
`a`. -/
def IsDerivationHom
    (d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M) :
    Prop :=
  Sheaf.ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
      prod.map d d ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M ∧
    Sheaf.ringMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
        leibnizHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M d ∧
      (prod.fst : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⨯
          Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⟶ _) ≫
        commRingSetHom a ≫ d =
        prod.snd ≫ commRingSetHom a ≫ d

/-- The morphism of sheaves of sets of a derivation is additive, stated diagrammatically. -/
lemma derivationSheafHom_add (d : M.val.Derivation' a.hom) :
    Sheaf.ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫
        derivationSheafHom a M d =
      prod.map (derivationSheafHom a M d) (derivationSheafHom a M d) ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J X) p,
    (Sheaf.sectionsFunctor J X).map_comp_apply, (Sheaf.sectionsFunctor J X).map_comp_apply,
    Sheaf.sectionsFunctor_map_ringAddHom, map_prodMap_apply, map_fst_prodObjMk,
    map_snd_prodObjMk, Sheaf.sectionsFunctor_map_moduleAddHom,
    sectionsFunctor_map_derivationSheafHom, sectionsFunctor_map_derivationSheafHom,
    sectionsFunctor_map_derivationSheafHom]
  exact d.d.map_add _ _

/-- The morphism of sheaves of sets of a derivation satisfies the Leibniz rule, stated
diagrammatically. -/
lemma derivationSheafHom_mul (d : M.val.Derivation' a.hom) :
    Sheaf.ringMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫
        derivationSheafHom a M d =
      leibnizHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M
        (derivationSheafHom a M d) := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor J X) p,
    (Sheaf.sectionsFunctor J X).map_comp_apply, Sheaf.sectionsFunctor_map_ringMulHom,
    sectionsFunctor_map_leibnizHom, sectionsFunctor_map_derivationSheafHom,
    sectionsFunctor_map_derivationSheafHom, sectionsFunctor_map_derivationSheafHom]
  exact d.d_mul _ _

/-- The morphism of sheaves of sets of a derivation is constant along the image of `a`, stated
diagrammatically. -/
lemma derivationSheafHom_base (d : M.val.Derivation' a.hom) :
    (prod.fst : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⨯
        Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⟶ _) ≫
        commRingSetHom a ≫ derivationSheafHom a M d =
      prod.snd ≫ commRingSetHom a ≫ derivationSheafHom a M d := by
  refine Sheaf.hom_ext_sections fun X p ↦ ?_
  rw [(Sheaf.sectionsFunctor J X).map_comp_apply, (Sheaf.sectionsFunctor J X).map_comp_apply,
    (Sheaf.sectionsFunctor J X).map_comp_apply, (Sheaf.sectionsFunctor J X).map_comp_apply,
    sectionsFunctor_map_derivationSheafHom, sectionsFunctor_map_derivationSheafHom]
  exact (d.d_app _).trans (d.d_app _).symm

variable {a M}

/-- Additivity of a morphism of sheaves of sets, read on sections. -/
lemma isDerivationHom_add_apply
    {d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M}
    (h : Sheaf.ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
      prod.map d d ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M)
    (X : Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor J X).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂))) :
    (Sheaf.sectionsFunctor J X).map d (x + y) =
      (Sheaf.sectionsFunctor J X).map d x + (Sheaf.sectionsFunctor J X).map d y := by
  have h' := congrArg (fun k ↦ (Sheaf.sectionsFunctor J X).map k (prodObjMk x y)) h
  simp only [(Sheaf.sectionsFunctor J X).map_comp_apply, Sheaf.sectionsFunctor_map_ringAddHom,
    map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    Sheaf.sectionsFunctor_map_moduleAddHom] at h'
  exact h'

/-- The Leibniz rule for a morphism of sheaves of sets, read on sections. -/
lemma isDerivationHom_mul_apply
    {d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M}
    (h : Sheaf.ringMulHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
      leibnizHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M d) (X : Cᵒᵖ)
    (x y : (Sheaf.sectionsFunctor J X).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂))) :
    (Sheaf.sectionsFunctor J X).map d (x * y) =
      x • (Sheaf.sectionsFunctor J X).map d y + y • (Sheaf.sectionsFunctor J X).map d x := by
  have h' := congrArg (fun k ↦ (Sheaf.sectionsFunctor J X).map k (prodObjMk x y)) h
  simp only [(Sheaf.sectionsFunctor J X).map_comp_apply, Sheaf.sectionsFunctor_map_ringMulHom,
    sectionsFunctor_map_leibnizHom] at h'
  exact h'

/-- A morphism of sheaves of sets which is additive sends the zero section to the zero
section. -/
lemma isDerivationHom_zero_apply
    {d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M}
    (h : Sheaf.ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
      prod.map d d ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M)
    (X : Cᵒᵖ) :
    (Sheaf.sectionsFunctor J X).map d
        (0 : (Sheaf.sectionsFunctor J X).obj
          (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂))) =
      0 := by
  have h0 := isDerivationHom_add_apply h X 0 0
  rw [add_zero] at h0
  exact (add_right_cancel ((zero_add _).trans h0)).symm

/-- A morphism of sheaves of sets which is additive and constant along the image of `a`
vanishes on that image. -/
lemma isDerivationHom_base_apply
    {d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M}
    (hadd : Sheaf.ringAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ≫ d =
      prod.map d d ≫
        Sheaf.moduleAddHom ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M)
    (hbase :
      (prod.fst : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⨯
          Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁) ⟶ _) ≫
          commRingSetHom a ≫ d =
        prod.snd ≫ commRingSetHom a ≫ d) (X : Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor J X).obj
      (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁))) :
    (Sheaf.sectionsFunctor J X).map d
        ((Sheaf.sectionsFunctor J X).map (commRingSetHom a) x) = 0 := by
  have h' := congrArg (fun k ↦ (Sheaf.sectionsFunctor J X).map k (prodObjMk x 0)) hbase
  simp only [(Sheaf.sectionsFunctor J X).map_comp_apply, map_fst_prodObjMk,
    map_snd_prodObjMk] at h'
  refine h'.trans ?_
  have hz : (Sheaf.sectionsFunctor J X).map (commRingSetHom a)
      (0 : (Sheaf.sectionsFunctor J X).obj
        (Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₁))) = 0 :=
    map_zero (a.hom.app X).hom
  rw [hz]
  exact isDerivationHom_zero_apply hadd X

/-- A morphism of the underlying sheaves of sets satisfying the three diagrammatic derivation
axioms is a derivation. -/
noncomputable def ofDerivationHom
    (d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
      Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M)
    (h : IsDerivationHom a M d) : M.val.Derivation' a.hom where
  d {X} := AddMonoidHom.mk' ((Sheaf.sectionsFunctor J X).map d)
    (isDerivationHom_add_apply h.1 X)
  d_mul {_} x y := isDerivationHom_mul_apply h.2.1 _ x y
  d_map {_ _} g x := (natTrans_app_map_apply (Sheaf.sectionsRestrict g) d x).symm
  d_app {_} x := isDerivationHom_base_apply h.1 h.2.2 _ x

variable (a M)

/-- Derivations of `M` over `a` are the same thing as morphisms of the underlying sheaves of
sets satisfying the three diagrammatic derivation axioms. -/
noncomputable def derivationHomEquiv :
    M.val.Derivation' a.hom ≃
      {d : Sheaf.ringSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) ⟶
        Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂) M //
        IsDerivationHom a M d} where
  toFun d := ⟨derivationSheafHom a M d, derivationSheafHom_add a M d,
    derivationSheafHom_mul a M d, derivationSheafHom_base a M d⟩
  invFun d := ofDerivationHom d.1 d.2
  left_inv _ := by ext X x; rfl
  right_inv _ := Subtype.ext rfl

/-- The morphism underlying `derivationHomEquiv a M d` is `derivationSheafHom a M d`. -/
@[simp]
lemma derivationHomEquiv_apply_coe (d : M.val.Derivation' a.hom) :
    (derivationHomEquiv a M d).1 = derivationSheafHom a M d := rfl

end DerivationHom

/-! ## Adjuncts of morphisms into a binary product -/

section Adjunct

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  [HasFiniteProducts E] [HasFiniteProducts F]
  {Φ : F ⥤ E} {Ψ : E ⥤ F} (adj : Φ ⊣ Ψ)

/-- The adjunct of a morphism into a binary product is the pair of the adjuncts of its two
components. Stated as a compatibility with the product comparison of `Ψ`, so that no inverse
appears. -/
lemma homEquiv_prodLift {A : F} {B₁ B₂ : E} (u : Φ.obj A ⟶ B₁) (v : Φ.obj A ⟶ B₂) :
    adj.homEquiv A (B₁ ⨯ B₂) (prod.lift u v) ≫ prodComparison Ψ B₁ B₂ =
      prod.lift (adj.homEquiv A B₁ u) (adj.homEquiv A B₂ v) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, ← adj.homEquiv_naturality_right, prod.lift_fst,
      prod.lift_fst]
  · rw [Category.assoc, prodComparison_snd, ← adj.homEquiv_naturality_right, prod.lift_snd,
      prod.lift_snd]

omit [HasFiniteProducts E] [HasFiniteProducts F] in
/-- The adjunct of `Φ` of a morphism, as a morphism into `Φ`'s value, is the morphism followed
by the unit. -/
lemma homEquiv_map {A A' : F} (g : A ⟶ A') :
    adj.homEquiv A (Φ.obj A') (Φ.map g) = g ≫ adj.unit.app A' := by
  rw [← adj.homEquiv_id, ← adj.homEquiv_naturality_left, Category.comp_id]

/-- The adjunct of a morphism into a binary product followed by a binary operation `n`, where
`n'` is the operation transported to `Ψ`, specified by its compatibility `hn` with the product
comparison. -/
lemma homEquiv_prodLift_comp {A : F} {B₁ B₂ B : E} (u : Φ.obj A ⟶ B₁) (v : Φ.obj A ⟶ B₂)
    (n : B₁ ⨯ B₂ ⟶ B) (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B)
    (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n) :
    adj.homEquiv A B (prod.lift u v ≫ n) =
      prod.lift (adj.homEquiv A B₁ u) (adj.homEquiv A B₂ v) ≫ n' := by
  rw [adj.homEquiv_naturality_right, ← hn, ← Category.assoc, homEquiv_prodLift adj]

/-- The adjunct of a Leibniz-shaped diagram. The diagram is built from a scalar multiplication
`sm` and an addition `ad` on the source side, and the two operations transported to `Ψ` appear
on the target side, the scalars there acting through the unit. -/
lemma homEquiv_prodComparison_leibniz {S : F} {T : E}
    (sm : Φ.obj S ⨯ T ⟶ T) (ad : T ⨯ T ⟶ T)
    (sm' : Ψ.obj (Φ.obj S) ⨯ Ψ.obj T ⟶ Ψ.obj T) (ad' : Ψ.obj T ⨯ Ψ.obj T ⟶ Ψ.obj T)
    (hsm : prodComparison Ψ (Φ.obj S) T ≫ sm' = Ψ.map sm)
    (had : prodComparison Ψ T T ≫ ad' = Ψ.map ad)
    (d : Φ.obj S ⟶ T) :
    adj.homEquiv (S ⨯ S) T (prodComparison Φ S S ≫
        (prod.lift (prod.lift prod.fst (prod.snd ≫ d) ≫ sm)
            (prod.lift prod.snd (prod.fst ≫ d) ≫ sm) ≫ ad)) =
      prod.lift (prod.lift (prod.fst ≫ adj.unit.app S) (prod.snd ≫ adj.homEquiv S T d) ≫ sm')
          (prod.lift (prod.snd ≫ adj.unit.app S) (prod.fst ≫ adj.homEquiv S T d) ≫ sm') ≫
        ad' := by
  simp only [prod.comp_lift_assoc, prodComparison_fst, prodComparison_snd,
    prodComparison_fst_assoc, prodComparison_snd_assoc]
  rw [homEquiv_prodLift_comp adj _ _ ad ad' had,
    homEquiv_prodLift_comp adj _ _ sm sm' hsm,
    homEquiv_prodLift_comp adj _ _ sm sm' hsm,
    homEquiv_map adj, homEquiv_map adj, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_left]
  rfl

/-- If the product comparison of `Φ` at `X, X` is invertible and `op'` is `Φ` of a binary
operation `op` transported along it, then `op' ≫ d = y` is equivalent to the same equation
after precomposing with `Φ.map op`. -/
private lemma comp_eq_iff_of_prodComparison {X : F} [IsIso (prodComparison Φ X X)] {op : X ⨯ X ⟶ X}
    {op' : Φ.obj X ⨯ Φ.obj X ⟶ Φ.obj X} (h : Φ.map op = prodComparison Φ X X ≫ op') {T : E}
    (d : Φ.obj X ⟶ T) (y : Φ.obj X ⨯ Φ.obj X ⟶ T) :
    op' ≫ d = y ↔ Φ.map op ≫ d = prodComparison Φ X X ≫ y := by
  rw [h, Category.assoc, cancel_epi]

end Adjunct

/-! ## Transposing the derivation axioms across `f⁻¹ ⊣ f_*` -/

section Transpose

universe w w' v u v' u'

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (R : Sheaf K RingCat.{w'})
  (M : SheafOfModules.{w} (inverseImageRingSheaf f R))

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The adjunct of `f⁻¹` of a morphism into the underlying sheaf of sets of `R` is that
morphism followed by the unit `R ⟶ f_*f⁻¹R`. -/
lemma homEquiv_inverseImage_map_ringUnit {Z : Sheaf K (Type w')}
    (g : Z ⟶ Sheaf.ringSheaf R) :
    f.adj.homEquiv Z (Sheaf.ringSheaf (inverseImageRingSheaf f R)) (f.inverseImage.map g) =
      g ≫ (sheafCompose K (forget RingCat.{w'})).map (ringUnit f R) :=
  (homEquiv_map f.adj g).trans
    (congrArg (fun m ↦ g ≫ m) (ringSheafMap_ringUnit f R).symm)

/-- Transposition carries the addition of an inverse-image sheaf of modules to the addition of
the direct image. -/
lemma homEquiv_moduleAddHom_lift {Z : Sheaf K (Type w')}
    (u v : f.inverseImage.obj Z ⟶ Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    f.adj.homEquiv Z (Sheaf.moduleSheaf (inverseImageRingSheaf f R) M)
        (prod.lift u v ≫ Sheaf.moduleAddHom (inverseImageRingSheaf f R) M) =
      prod.lift (f.adj.homEquiv Z _ u) (f.adj.homEquiv Z _ v) ≫
        Sheaf.moduleAddHom R ((directImageModules f R).obj M) :=
  homEquiv_prodLift_comp f.adj u v (Sheaf.moduleAddHom (inverseImageRingSheaf f R) M) _
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f R) M).symm

/-- Transposition carries the scalar multiplication of an inverse-image sheaf of modules to the
scalar multiplication of the direct image. -/
lemma homEquiv_moduleSMulHom_lift {Z : Sheaf K (Type w')}
    (r : f.inverseImage.obj Z ⟶ Sheaf.ringSheaf (inverseImageRingSheaf f R))
    (u : f.inverseImage.obj Z ⟶ Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    f.adj.homEquiv Z (Sheaf.moduleSheaf (inverseImageRingSheaf f R) M)
        (prod.lift r u ≫ Sheaf.moduleSMulHom (inverseImageRingSheaf f R) M) =
      prod.lift (f.adj.homEquiv Z _ r) (f.adj.homEquiv Z _ u) ≫
        Sheaf.moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f R))
          ((pushforwardModuleFunctor f (inverseImageRingSheaf f R)).obj M) :=
  homEquiv_prodLift_comp f.adj r u (Sheaf.moduleSMulHom (inverseImageRingSheaf f R) M) _
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f R) M).symm

/-- The scalar multiplication of the direct image, read through the unit `R ⟶ f_*f⁻¹R`: the
scalars act on the direct image by restriction of scalars along that unit. -/
lemma prodLift_moduleSMulHom_directImageModules {Z : Sheaf K (Type w')}
    (p : Z ⟶ Sheaf.ringSheaf R)
    (q : Z ⟶ Sheaf.moduleSheaf R ((directImageModules f R).obj M)) :
    prod.lift p q ≫ Sheaf.moduleSMulHom R ((directImageModules f R).obj M) =
      prod.lift (p ≫ (sheafCompose K (forget RingCat.{w'})).map (ringUnit f R)) q ≫
        Sheaf.moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f R))
          ((pushforwardModuleFunctor f (inverseImageRingSheaf f R)).obj M) :=
  (congrArg (fun m ↦ prod.lift p q ≫ m)
      (moduleSMulHom_restrictScalars (ringUnit f R)
        ((pushforwardModuleFunctor f (inverseImageRingSheaf f R)).obj M))).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg
        (fun m ↦ m ≫ Sheaf.moduleSMulHom
          (pushforwardRingSheaf f (inverseImageRingSheaf f R))
          ((pushforwardModuleFunctor f (inverseImageRingSheaf f R)).obj M))
        ((prod.lift_map p q _ _).trans
          (congrArg
            (fun m ↦ prod.lift (p ≫ (sheafCompose K (forget RingCat.{w'})).map (ringUnit f R)) m)
            (Category.comp_id q)))))

/-- Additivity of a morphism out of the underlying sheaf of sets of an inverse-image sheaf of
rings is equivalent to additivity of its adjunct. -/
lemma homEquiv_ringAddHom_iff
    (d : Sheaf.ringSheaf (inverseImageRingSheaf f R) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    Sheaf.ringAddHom (inverseImageRingSheaf f R) ≫ d =
        prod.map d d ≫ Sheaf.moduleAddHom (inverseImageRingSheaf f R) M ↔
      Sheaf.ringAddHom R ≫ f.adj.homEquiv _ _ d =
        prod.map (f.adj.homEquiv _ _ d) (f.adj.homEquiv _ _ d) ≫
          Sheaf.moduleAddHom R ((directImageModules f R).obj M) := by
  have := isIso_prodComparison_inverseImage f (Sheaf.ringSheaf R) (Sheaf.ringSheaf R)
  exact (comp_eq_iff_of_prodComparison (Φ := f.inverseImage)
    (ringAdd_map_aux' J f.inverseImage R) d _).trans
    (homEquiv_binary_iff f.adj d d d (Sheaf.ringAddHom R)
      (Sheaf.moduleAddHom (inverseImageRingSheaf f R) M) _
      (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f R) M).symm)

/-- Transposition carries the Leibniz diagram over `f⁻¹R` to the Leibniz diagram over `R`. -/
lemma homEquiv_leibnizHom
    (d : Sheaf.ringSheaf (inverseImageRingSheaf f R) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    f.adj.homEquiv (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R) _
        (prodComparison f.inverseImage (Sheaf.ringSheaf R) (Sheaf.ringSheaf R) ≫
          leibnizHom (inverseImageRingSheaf f R) M d) =
      leibnizHom R ((directImageModules f R).obj M) (f.adj.homEquiv _ _ d) := by
  refine Eq.trans (homEquiv_prodComparison_leibniz f.adj
    (Sheaf.moduleSMulHom (inverseImageRingSheaf f R) M)
    (Sheaf.moduleAddHom (inverseImageRingSheaf f R) M)
    (Sheaf.moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f R))
      ((pushforwardModuleFunctor f (inverseImageRingSheaf f R)).obj M))
    (Sheaf.moduleAddHom R ((directImageModules f R).obj M))
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f R) M).symm
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f R) M).symm d) ?_
  rw [leibnizHom_eq R ((directImageModules f R).obj M) (f.adj.homEquiv _ _ d),
    prodLift_moduleSMulHom_directImageModules f R M,
    prodLift_moduleSMulHom_directImageModules f R M, ringSheafMap_ringUnit]
  rfl

/-- The Leibniz rule for a morphism out of the underlying sheaf of sets of an inverse-image
sheaf of rings is equivalent to the Leibniz rule for its adjunct. -/
lemma homEquiv_ringMulHom_iff
    (d : Sheaf.ringSheaf (inverseImageRingSheaf f R) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    Sheaf.ringMulHom (inverseImageRingSheaf f R) ≫ d =
        leibnizHom (inverseImageRingSheaf f R) M d ↔
      Sheaf.ringMulHom R ≫ f.adj.homEquiv _ _ d =
        leibnizHom R ((directImageModules f R).obj M) (f.adj.homEquiv _ _ d) := by
  have := isIso_prodComparison_inverseImage f (Sheaf.ringSheaf R) (Sheaf.ringSheaf R)
  have h1 := comp_eq_iff_of_prodComparison (Φ := f.inverseImage)
    (ringMul_map_aux' J f.inverseImage R) d (leibnizHom (inverseImageRingSheaf f R) M d)
  have hA := f.adj.homEquiv_naturality_left (Sheaf.ringMulHom R) d
  refine h1.trans (((f.adj.homEquiv (Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R)
    (Sheaf.moduleSheaf (inverseImageRingSheaf f R) M)).apply_eq_iff_eq).symm.trans ?_)
  rw [hA, homEquiv_leibnizHom f R M]

omit [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- A morphism out of an inverse image is constant exactly when its adjunct is. Constancy of a
morphism `β` is expressed, with no zero and no terminal object, as the equality of the two
composites with the projections of a binary product. -/
lemma homEquiv_constant_iff {B : Sheaf K (Type w')}
    (β : f.inverseImage.obj B ⟶ Sheaf.moduleSheaf (inverseImageRingSheaf f R) M) :
    (prod.fst : f.inverseImage.obj B ⨯ f.inverseImage.obj B ⟶ _) ≫ β = prod.snd ≫ β ↔
      (prod.fst : B ⨯ B ⟶ B) ≫ f.adj.homEquiv B _ β =
        prod.snd ≫ f.adj.homEquiv B _ β := by
  have := isIso_prodComparison_inverseImage f B B
  refine Iff.trans (cancel_epi (prodComparison f.inverseImage B B)).symm ?_
  rw [prodComparison_fst_assoc, prodComparison_snd_assoc]
  refine Iff.trans ((f.adj.homEquiv (B ⨯ B)
    (Sheaf.moduleSheaf (inverseImageRingSheaf f R) M)).apply_eq_iff_eq).symm ?_
  rw [f.adj.homEquiv_naturality_left (prod.fst : B ⨯ B ⟶ B) β,
    f.adj.homEquiv_naturality_left (prod.snd : B ⨯ B ⟶ B) β]

end Transpose

/-! ## The transposition -/

section DerivationTranspose

universe w w' v u v' u'

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {A P : Sheaf K CommRingCat.{w'}} (a : A ⟶ P)
  (M : SheafOfModules.{w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) (f.inverseImageRing.obj P)))

/-- The underlying morphism of sheaves of sets of the inverse image of `a` is the inverse image
of the underlying morphism of `a`. The topologies are rebound so that the instance variables of
the section stay out of scope. -/
private lemma commRingSetHom_inverseImageRing_map {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    {A P : Sheaf K CommRingCat.{w'}} (a : A ⟶ P) :
    commRingSetHom.{w, v, u} (f.inverseImageRing.map a) =
      f.inverseImage.map (commRingSetHom.{w', v', u'} a) :=
  (congrArg (sheafCompose J (forget RingCat.{w})).map
      (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage a)).trans
    (ringSheafMap_pullbackRingSheafMap J f.inverseImage
      ((Stacks.forgetCommRingSheaf.{v', u', w'} K).map a))

/-- A morphism of the underlying sheaves of sets is a derivation over the inverse image of `a`
exactly when its adjunct is a derivation over `a`. -/
lemma isDerivationHom_transpose_iff
    (d : Sheaf.ringSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) (f.inverseImageRing.obj P)) ⟶
      Sheaf.moduleSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J))
          (f.inverseImageRing.obj P)) M) :
    IsDerivationHom (f.inverseImageRing.map a) M d ↔
      IsDerivationHom a
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).obj M)
        (f.adj.homEquiv _ _ d) := by
  unfold IsDerivationHom
  rw [commRingSetHom_inverseImageRing_map]
  refine and_congr
    (homEquiv_ringAddHom_iff f
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P) M d)
    (and_congr
      (homEquiv_ringMulHom_iff f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P) M d) ?_)
  refine Iff.trans
    (homEquiv_constant_iff f ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P) M
      (f.inverseImage.map (commRingSetHom a) ≫ d)) ?_
  erw [f.adj.homEquiv_naturality_left]
  rfl

/-- **Inverse image of sheaves of modules transposes derivations.** For a morphism of topoi
`f`, a morphism `a : A ⟶ P` of sheaves of commutative rings on the target and a sheaf of
modules `M` over the inverse image of `P`, the derivations of `M` over the inverse image of `a`
are the derivations of the direct image of `M` over `a`:
`Der_{f⁻¹A}(f⁻¹P, M) = Der_A(P, f_*M)`.

This is the module-level half of Stacks 08TQ, and the transposition is the hom-set bijection of
Stacks 03D3 (`Stacks.Sheaves.RingedToposModules.toposModulesHomEquiv`) read on underlying
sheaves of sets. -/
noncomputable def inverseImageDerivationEquiv :
    M.val.Derivation' (f.inverseImageRing.map a).hom ≃
      ((directImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).obj M).val.Derivation'
        a.hom :=
  (derivationHomEquiv (f.inverseImageRing.map a) M).trans
    ((Equiv.subtypeEquiv (f.adj.homEquiv _ _) (isDerivationHom_transpose_iff f a M)).trans
      (derivationHomEquiv a
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).obj M)).symm)

/-- `inverseImageDerivationEquiv` is the hom-set bijection of `f⁻¹ ⊣ f_*` on the morphisms of
underlying sheaves of sets belonging to the two derivations. -/
lemma derivationSheafHom_inverseImageDerivationEquiv
    (d : M.val.Derivation' (f.inverseImageRing.map a).hom) :
    derivationSheafHom a
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).obj M)
        (inverseImageDerivationEquiv f a M d) =
      f.adj.homEquiv _ _ (derivationSheafHom (f.inverseImageRing.map a) M d) :=
  rfl

end DerivationTranspose

/-! ## Naturality of the transposition -/

section TransposeNaturality

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (a : O₁ ⟶ O₂)
  {M N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂)}

/-- The morphism of underlying sheaves of sets of a derivation postcomposed with a morphism of
sheaves of modules is that of the derivation, followed by the morphism. -/
lemma derivationSheafHom_postcomp (k : M ⟶ N) (d : M.val.Derivation' a.hom) :
    derivationSheafHom a N (d.postcomp k.val) =
      derivationSheafHom a M d ≫
        (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) O₂)).map k :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

section Transpose

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w' v' u'

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {A P : Sheaf K CommRingCat.{w'}} (b : A ⟶ P)
  {M' N' : SheafOfModules.{w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) (f.inverseImageRing.obj P))}

/-- The transposition of derivations is natural in the coefficient module. -/
lemma inverseImageDerivationEquiv_postcomp (k : M' ⟶ N')
    (d : M'.val.Derivation' (f.inverseImageRing.map b).hom) :
    inverseImageDerivationEquiv f b N' (d.postcomp k.val) =
      (inverseImageDerivationEquiv f b M' d).postcomp
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).map k).val := by
  refine (derivationHomEquiv b _).injective (Subtype.ext ?_)
  rw [derivationHomEquiv_apply_coe, derivationHomEquiv_apply_coe,
    derivationSheafHom_inverseImageDerivationEquiv, derivationSheafHom_postcomp,
    derivationSheafHom_postcomp, derivationSheafHom_inverseImageDerivationEquiv]
  refine (f.adj.homEquiv_naturality_right _ _).trans ?_
  congr 1

/-- The inverse transposition of derivations is natural in the coefficient module. -/
lemma inverseImageDerivationEquiv_symm_postcomp (k : M' ⟶ N')
    (D : ((directImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).obj M').val.Derivation'
      b.hom) :
    ((inverseImageDerivationEquiv f b M').symm D).postcomp k.val =
      (inverseImageDerivationEquiv f b N').symm
        (D.postcomp
          ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P)).map k).val) := by
  refine ((inverseImageDerivationEquiv f b N').eq_symm_apply).mpr ?_
  rw [inverseImageDerivationEquiv_postcomp, Equiv.apply_symm_apply]

/-- The hom-set bijection of `f⁻¹ ⊣ f_*` for sheaves of modules is natural in the target. -/
lemma toposModulesHomEquiv_naturality_right
    (O : Sheaf K RingCat.{w'}) (G : SheafOfModules.{w'} O)
    {F F' : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (α : (inverseImageModules f O).obj G ⟶ F) (g : F ⟶ F') :
    toposModulesHomEquiv f O G F' (α ≫ g) =
      toposModulesHomEquiv f O G F α ≫ (directImageModules f O).map g := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [moduleSheafFunctor_map_toposModulesHomEquiv, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_toposModulesHomEquiv,
    moduleSheafFunctor_map_directImageModules_map]
  exact f.adj.homEquiv_naturality_right _ _

end Transpose

section PrecompSheafHom

variable {A : Sheaf J CommRingCat.{w}} {a₁ : A ⟶ O₁} {a₂ : A ⟶ O₂}

/-- The morphism of underlying sheaves of sets of a derivation precomposed with a morphism `q`
of sheaves of commutative rings is the underlying morphism of `q`, followed by that of the
derivation. -/
lemma derivationSheafHom_precomp (q : O₁ ⟶ O₂) (d : M.val.Derivation' a₂.hom)
    (h : a₁.hom ≫ q.hom = a₂.hom) :
    derivationSheafHom a₁
        ((SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, w} J).map q)).obj M) (d.precomp q.hom h) =
      commRingSetHom q ≫ derivationSheafHom a₂ M d :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end PrecompSheafHom

section RingNaturality

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w' v' u'

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  {A P₁ P₂ : Sheaf K CommRingCat.{w'}} {a₁ : A ⟶ P₁} {a₂ : A ⟶ P₂} (q : P₁ ⟶ P₂)
  (M' : SheafOfModules.{w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} (J := J)) (f.inverseImageRing.obj P₂)))

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The inverse image of a commuting triangle `a₁ ≫ q = a₂` of sheaves of commutative rings,
read on underlying presheaves. -/
lemma inverseImageRing_map_hom_comp (hq : a₁ ≫ q = a₂) :
    (f.inverseImageRing.map a₁).hom ≫ (f.inverseImageRing.map q).hom =
      (f.inverseImageRing.map a₂).hom := by
  rw [← hq, Functor.map_comp]
  rfl

/-- **The transposition of derivations is natural in the sheaf of commutative rings.** For
`q : P₁ ⟶ P₂` under `A`, transposing a derivation of `M` over `f⁻¹a₂` and then precomposing by
`q` is precomposing by `f⁻¹q` and then transposing, as morphisms of the underlying sheaves of
sets.

The coefficient module is fixed over `f⁻¹P₂`, the derivations over `f⁻¹a₁` taking values in it
by restriction of scalars along `f⁻¹q`. The two derivations themselves cannot be compared: the
direct image of the restriction and the restriction of the direct image carry the two scalar
actions of `P₁` on `f_*M` obtained from the two sides of the naturality square of the unit
`P₁ ⟶ f_*f⁻¹P₁`, and that square does not hold definitionally. Since `derivationSheafHom` is
injective for fixed base morphism and coefficient module, the equation below determines the
derivation. -/
lemma derivationSheafHom_inverseImageDerivationEquiv_precomp (hq : a₁ ≫ q = a₂)
    (d : M'.val.Derivation' (f.inverseImageRing.map a₂).hom) :
    derivationSheafHom.{w', v', u'} a₁
        ((directImageModules f
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P₁)).obj
          ((SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf.{v, u, w} J).map
            (f.inverseImageRing.map q))).obj M'))
        (inverseImageDerivationEquiv.{w, w', v, u, v', u'} f a₁
          ((SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf.{v, u, w} J).map
            (f.inverseImageRing.map q))).obj M')
          (d.precomp (f.inverseImageRing.map q).hom
            (inverseImageRing_map_hom_comp f q hq))) =
      commRingSetHom.{w', v', u'} q ≫
        derivationSheafHom.{w', v', u'} a₂
          ((directImageModules f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w'} (J := K)) P₂)).obj M')
          (inverseImageDerivationEquiv.{w, w', v, u, v', u'} f a₂ M' d) := by
  refine Eq.trans ?_ (f.adj.homEquiv_naturality_left _ _)
  rw [← commRingSetHom_inverseImageRing_map f q]
  rfl

/-- Naturality of the transposition in the sheaf of commutative rings, read on sections: the
transpose of the precomposition of `d` by `f⁻¹q` takes a section `x` of `P₁` to the value of
the transpose of `d` at `q x`. -/
lemma inverseImageDerivationEquiv_precomp_d (hq : a₁ ≫ q = a₂)
    (d : M'.val.Derivation' (f.inverseImageRing.map a₂).hom) (X : Dᵒᵖ) (x : P₁.obj.obj X) :
    (inverseImageDerivationEquiv.{w, w', v, u, v', u'} f a₁
          ((SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf.{v, u, w} J).map
            (f.inverseImageRing.map q))).obj M')
          (d.precomp (f.inverseImageRing.map q).hom
            (inverseImageRing_map_hom_comp f q hq))).d x =
      (inverseImageDerivationEquiv.{w, w', v, u, v', u'} f a₂ M' d).d ((q.hom.app X).hom x) :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor K X).map m x)
    (derivationSheafHom_inverseImageDerivationEquiv_precomp f q M' hq d)

end RingNaturality

end TransposeNaturality

/-! ## The inverse image of the sheaf of relative differentials -/

section Differentials

open AlgebraicGeometry.SheafOfModules (derivationsFunctor moduleOfDifferentialsOfSite
  universalDerivationOfSite corepresentableByIso)
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A P : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ P)

/-- The inverse image of the sheaf of relative differentials `Ω_{P/A}`, as a sheaf of modules
over the inverse image of `P`. -/
noncomputable abbrev inverseImageDifferentials :
    SheafOfModules.{max u v w}
      (inverseImageRingSheaf f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P)) :=
  (inverseImageModules f
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P)).obj
    (moduleOfDifferentialsOfSite.{v', u', max u' v' w', max u' v' w'} A P a)

/-- The inverse image of `Ω_{P/A}` corepresents the `f⁻¹A`-derivations of `f⁻¹P`: a morphism out
of it is, by `f⁻¹ ⊣ f_*` and the universal property of `Ω_{P/A}`, an `A`-derivation of `P` with
values in the direct image, that is an `f⁻¹A`-derivation of `f⁻¹P`. -/
noncomputable def inverseImageDifferentialsCorepresentableBy :
    (derivationsFunctor.{max u v w} (f.inverseImageRing.obj A) (f.inverseImageRing.obj P)
        (f.inverseImageRing.map a)).CorepresentableBy (inverseImageDifferentials f a) where
  homEquiv {F} :=
    (toposModulesHomEquiv f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P) _ F).trans
      ((derivationsFunctor.{max u' v' w'} A P a).corepresentableBy.homEquiv.trans
        (inverseImageDerivationEquiv f a F).symm)
  homEquiv_comp {F F'} g h := by
    change (inverseImageDerivationEquiv f a F').symm
        ((derivationsFunctor.{max u' v' w'} A P a).corepresentableBy.homEquiv
          (toposModulesHomEquiv f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P) _ F'
            (h ≫ g))) =
      ((inverseImageDerivationEquiv f a F).symm
        ((derivationsFunctor.{max u' v' w'} A P a).corepresentableBy.homEquiv
          (toposModulesHomEquiv f
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P) _ F
            h))).postcomp g.val
    refine Eq.trans (congrArg (fun z => (inverseImageDerivationEquiv f a F').symm
        ((derivationsFunctor.{max u' v' w'} A P a).corepresentableBy.homEquiv z))
      (toposModulesHomEquiv_naturality_right f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) P) _ h g)) ?_
    refine Eq.trans (congrArg (fun z => (inverseImageDerivationEquiv f a F').symm z)
      ((derivationsFunctor.{max u' v' w'} A P a).corepresentableBy.homEquiv_comp _ _)) ?_
    exact (inverseImageDerivationEquiv_symm_postcomp f a g _).symm

/-- **Stacks 08TQ.** The inverse image of the sheaf of relative differentials of a homomorphism
of sheaves of commutative rings along a morphism of topoi is the sheaf of relative differentials
of the inverse image: `f⁻¹Ω_{P/A} ≅ Ω_{f⁻¹P/f⁻¹A}`. -/
@[stacks 08TQ "for an arbitrary morphism of topoi, with the object, arrow and section universes
of the two sites independent"]
noncomputable def inverseImageDifferentialsIso :
    inverseImageDifferentials f a ≅
      moduleOfDifferentialsOfSite.{v, u, max u v w, max u v w}
        (f.inverseImageRing.obj A) (f.inverseImageRing.obj P) (f.inverseImageRing.map a) :=
  corepresentableByIso (inverseImageDifferentialsCorepresentableBy f a)
    (derivationsFunctor.{max u v w} (f.inverseImageRing.obj A) (f.inverseImageRing.obj P)
      (f.inverseImageRing.map a)).corepresentableBy

/-- **Stacks 08TQ.** The identification is the one carrying the inverse image of the universal
derivation of `Ω_{P/A}` to the universal derivation of `Ω_{f⁻¹P/f⁻¹A}`: transposing it along
`f⁻¹ ⊣ f_*` and the universal property of `Ω_{P/A}` returns the universal derivation. -/
@[stacks 08TQ "compatibility with the universal derivations"]
lemma homEquiv_inverseImageDifferentialsIso_hom :
    (inverseImageDifferentialsCorepresentableBy f a).homEquiv
        (inverseImageDifferentialsIso f a).hom =
      universalDerivationOfSite.{v, u, max u v w, max u v w}
        (f.inverseImageRing.obj A) (f.inverseImageRing.obj P) (f.inverseImageRing.map a) :=
  (inverseImageDifferentialsCorepresentableBy f a).homEquiv.apply_symm_apply _

end Differentials

end Stacks.Sheaves.RingedToposModules
