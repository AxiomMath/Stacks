module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChange

/-!
# The composition law for the base-changed graded algebra

Let `q : T' ⟶ T` and `g : T ⟶ S` be morphisms of schemes and let `𝒜` be a sheaf of `ℤ`-graded
`𝒪_S`-algebras. Base changing along `g` and then along `q`
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebra`) gives a sheaf of graded
`𝒪_{T'}`-algebras, and so does base changing along `q ≫ g`; the two are not equal, because the
pieces are the two sides of the pseudofunctoriality isomorphism of the inverse image. This file
identifies them as a **unital homomorphism of sheaves of graded algebras**, and proves its two
coherences: the comparison along an identity, and the cocycle condition for a triple composite.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHom`: **the composition law**,
  `(q ≫ g)^*𝒜 ⟵ q^*(g^*𝒜)` as a unital homomorphism, degreewise
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomInv`: its inverse.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf`: the same for a named
  composite `π` with `q ≫ g = π`, and `baseAlgebraCompHomOfInv` its inverse.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCongrHom`: the comparison of the
  base changes along two equal morphisms.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraMapHom`: the inverse image of a
  unital homomorphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isIso_baseAlgebraCompHom_app` and
  `isIso_baseAlgebraCompHomOf_app`: every component of the composition law is an isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf_app`: the components are
  the canonical comparison `Stacks.AlgebraicGeometry.ModuleLimits.canHom` of an iterated inverse
  image.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf_cocycle`: **the cocycle
  condition**, for a chain `T'' ⟶ T' ⟶ T ⟶ S`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf_id_left_app` and
  `baseAlgebraCompHomOf_id_right_app`: **the identity coherences**, in the two variables.

## Implementation notes

`Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso` is the
identification as an isomorphism in the category of sheaves of graded algebras, whose morphisms
`SheafOfModules.GradedAlgebra.Hom` ask multiplicativity but not unitality, and
`pullbackGradedAlgebraCompIso_one_eval` is its unitality. So the composition law is
`SheafOfModules.GradedAlgebra.UnitalHom.ofHom` applied to the two, and
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebra g 𝒜` is
`Stacks.RingedSpace.pullbackGradedAlgebra (ringedSpaceHom g) 𝒜` by definition, so no transport
intervenes.

On components, `baseAlgebraMapHom` is `Stacks.RingedSpace.pullbackGradedAlgebraMap`; its unit
law is the value of the unit over the whole space together with naturality.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

variable {T' T S : Scheme.{u}}

/-! ### The inverse image of a unital homomorphism -/

section Map

variable {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-- The inverse image along `g` of a unital homomorphism carries the unit of `g^*A` to the unit
of `g^*B`. The unit of an inverse image is the inverse-image-unit image of the unit over the
whole space, restricted to every open, so the statement is the one over the whole space together
with naturality of the component in degree zero. -/
theorem baseAlgebraMap_one_eval (g : T ⟶ S) (Φ : UnitalHom A B)
    (U : (Opens T.carrier)ᵒᵖ) :
    ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val.app U
        ((baseAlgebra g A).one.eval U) = (baseAlgebra g B).one.eval U := by
  obtain ⟨U⟩ := U
  have htop : ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val.app
        (op (⊤ : Opens T.carrier)) ((baseAlgebra g A).one.eval (op ⊤)) =
      (baseAlgebra g B).one.eval (op (⊤ : Opens T.carrier)) := by
    have h1 : (baseAlgebra g A).one.eval (op (⊤ : Opens T.carrier)) =
        pullbackUnit (ringedSpaceHom g) (A.piece 0) (op (⊤ : Opens S.carrier))
          (A.one.eval (op (⊤ : Opens S.carrier))) :=
      pullbackSectionsUnit_eval (ringedSpaceHom g) (A.piece 0) A.one ⊤
    have h2 : (baseAlgebra g B).one.eval (op (⊤ : Opens T.carrier)) =
        pullbackUnit (ringedSpaceHom g) (B.piece 0) (op (⊤ : Opens S.carrier))
          (B.one.eval (op (⊤ : Opens S.carrier))) :=
      pullbackSectionsUnit_eval (ringedSpaceHom g) (B.piece 0) B.one ⊤
    have h3 : ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val.app
          (op (⊤ : Opens T.carrier))
          (pullbackUnit (ringedSpaceHom g) (A.piece 0) (op (⊤ : Opens S.carrier))
            (A.one.eval (op (⊤ : Opens S.carrier)))) =
        pullbackUnit (ringedSpaceHom g) (B.piece 0) (op (⊤ : Opens S.carrier))
          ((Φ.app 0).val.app (op (⊤ : Opens S.carrier))
            (A.one.eval (op (⊤ : Opens S.carrier)))) :=
      pullbackUnit_naturality (ringedSpaceHom g) (Φ.app 0) (op (⊤ : Opens S.carrier))
        (A.one.eval (op (⊤ : Opens S.carrier)))
    have h4 : (Φ.app 0).val.app (op (⊤ : Opens S.carrier))
          (A.one.eval (op (⊤ : Opens S.carrier))) =
        B.one.eval (op (⊤ : Opens S.carrier)) := Φ.map_one (op (⊤ : Opens S.carrier))
    rw [h1, h3, h4, h2]
  have hres : (baseAlgebra g A).one.eval (op U) =
      ((baseAlgebra g A).piece 0).val.map (homOfLE (le_top : U ≤ ⊤)).op
        ((baseAlgebra g A).one.eval (op ⊤)) :=
    (PresheafOfModules.sections_property (baseAlgebra g A).one
      (homOfLE (le_top : U ≤ ⊤)).op).symm
  have hnat : ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val.app (op U)
        (((baseAlgebra g A).piece 0).val.map (homOfLE (le_top : U ≤ ⊤)).op
          ((baseAlgebra g A).one.eval (op ⊤))) =
      ((baseAlgebra g B).piece 0).val.map (homOfLE (le_top : U ≤ ⊤)).op
        (((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val.app (op ⊤)
          ((baseAlgebra g A).one.eval (op ⊤))) :=
    PresheafOfModules.naturality_apply
      ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app 0)).val
      (homOfLE (le_top : U ≤ ⊤)).op ((baseAlgebra g A).one.eval (op ⊤))
  rw [hres, hnat, htop]
  exact PresheafOfModules.sections_property (baseAlgebra g B).one
    (homOfLE (le_top : U ≤ ⊤)).op

/-- **The inverse image of a unital homomorphism of sheaves of graded algebras**, degreewise the
inverse image of its components. Multiplicativity is
`Stacks.RingedSpace.pullbackGradedAlgebraMap`; the unit law is `baseAlgebraMap_one_eval`. -/
def baseAlgebraMapHom (g : T ⟶ S) (Φ : UnitalHom A B) :
    UnitalHom (baseAlgebra g A) (baseAlgebra g B) :=
  UnitalHom.ofHom (pullbackGradedAlgebraMap (ringedSpaceHom g) Φ.toHom)
    ((UnitalHom.map_one_iff _).1 (baseAlgebraMap_one_eval g Φ))

/-- The component in degree `n` of `baseAlgebraMapHom g Φ` is the inverse image of `Φ.app n`. -/
@[simp] theorem baseAlgebraMapHom_app (g : T ⟶ S) (Φ : UnitalHom A B) (n : ℤ) :
    (baseAlgebraMapHom g Φ).app n = (pullbackFunctor (ringedSpaceHom g)).map (Φ.app n) := rfl

/-- The inverse image of a degreewise invertible unital homomorphism is degreewise invertible. -/
instance isIso_baseAlgebraMapHom_app (g : T ⟶ S) (Φ : UnitalHom A B) (n : ℤ)
    [IsIso (Φ.app n)] : IsIso ((baseAlgebraMapHom g Φ).app n) :=
  inferInstanceAs (IsIso ((pullbackFunctor (ringedSpaceHom g)).map (Φ.app n)))

end Map

/-! ### The composition law -/

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))

/-- **The composition law for the base-changed graded algebra.** For `q : T' ⟶ T` and
`g : T ⟶ S`, base changing along `g` and then along `q` agrees with base changing along `q ≫ g`,
as sheaves of graded algebras: a unital homomorphism whose component in degree `n` is the
pseudofunctoriality isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp q g` of the
inverse image at `𝒜ₙ`.

Multiplicativity is
`Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso` and unitality
is `pullbackGradedAlgebraCompIso_one_eval`. -/
def baseAlgebraCompHom (q : T' ⟶ T) (g : T ⟶ S) :
    UnitalHom (baseAlgebra q (baseAlgebra g A)) (baseAlgebra (q ≫ g) A) :=
  UnitalHom.ofHom (pullbackGradedAlgebraCompIso A q g).hom
    ((UnitalHom.map_one_iff _).1 (pullbackGradedAlgebraCompIso_one_eval A q g))

/-- The component in degree `n` of the composition law is
`AlgebraicGeometry.Scheme.Modules.pullbackComp q g` at `A.piece n`. -/
@[simp] theorem baseAlgebraCompHom_app (q : T' ⟶ T) (g : T ⟶ S) (n : ℤ) :
    (baseAlgebraCompHom A q g).app n = (Scheme.Modules.pullbackComp q g).hom.app (A.piece n) :=
  rfl

/-- Every component of the composition law is an isomorphism. -/
instance isIso_baseAlgebraCompHom_app (q : T' ⟶ T) (g : T ⟶ S) (n : ℤ) :
    IsIso ((baseAlgebraCompHom A q g).app n) :=
  inferInstanceAs (IsIso ((Scheme.Modules.pullbackComp q g).app (A.piece n)).hom)

/-- **The inverse of the composition law**, again a unital homomorphism. -/
def baseAlgebraCompHomInv (q : T' ⟶ T) (g : T ⟶ S) :
    UnitalHom (baseAlgebra (q ≫ g) A) (baseAlgebra q (baseAlgebra g A)) :=
  (baseAlgebraCompHom A q g).inverse

/-- The component in degree `n` of the inverse of the composition law is the inverse of the
component of the composition law. -/
@[simp] theorem baseAlgebraCompHomInv_app (q : T' ⟶ T) (g : T ⟶ S) (n : ℤ) :
    (baseAlgebraCompHomInv A q g).app n = inv ((baseAlgebraCompHom A q g).app n) := rfl

/-- Every component of the inverse of the composition law is an isomorphism. -/
instance isIso_baseAlgebraCompHomInv_app (q : T' ⟶ T) (g : T ⟶ S) (n : ℤ) :
    IsIso ((baseAlgebraCompHomInv A q g).app n) :=
  inferInstanceAs (IsIso (inv ((baseAlgebraCompHom A q g).app n)))

/-- The two composites of the composition law with its inverse are the identity. -/
theorem baseAlgebraCompHom_comp_inv (q : T' ⟶ T) (g : T ⟶ S) :
    (baseAlgebraCompHom A q g).comp (baseAlgebraCompHomInv A q g) =
      UnitalHom.id (baseAlgebra q (baseAlgebra g A)) :=
  (baseAlgebraCompHom A q g).comp_inverse

/-- The two composites of the composition law with its inverse are the identity. -/
theorem baseAlgebraCompHomInv_comp (q : T' ⟶ T) (g : T ⟶ S) :
    (baseAlgebraCompHomInv A q g).comp (baseAlgebraCompHom A q g) =
      UnitalHom.id (baseAlgebra (q ≫ g) A) :=
  (baseAlgebraCompHom A q g).inverse_comp

/-! ### The composition law at a named composite -/

/-- **Base changing along two equal morphisms agrees**, as a unital homomorphism, degreewise
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
def baseAlgebraCongrHom {f f' : T ⟶ S} (hff : f = f') :
    UnitalHom (baseAlgebra f A) (baseAlgebra f' A) :=
  UnitalHom.ofHom (pullbackGradedAlgebraCongrIso A hff).hom
    ((UnitalHom.map_one_iff _).1 (pullbackGradedAlgebraCongrIso_one_eval A hff))

/-- The component in degree `n` of `baseAlgebraCongrHom A hff` is
`AlgebraicGeometry.Scheme.Modules.pullbackCongr hff` at `A.piece n`. -/
@[simp] theorem baseAlgebraCongrHom_app {f f' : T ⟶ S} (hff : f = f') (n : ℤ) :
    (baseAlgebraCongrHom A hff).app n = (Scheme.Modules.pullbackCongr hff).hom.app (A.piece n) :=
  rfl

/-- Every component of `baseAlgebraCongrHom A hff` is an isomorphism. -/
instance isIso_baseAlgebraCongrHom_app {f f' : T ⟶ S} (hff : f = f') (n : ℤ) :
    IsIso ((baseAlgebraCongrHom A hff).app n) :=
  inferInstanceAs (IsIso ((Scheme.Modules.pullbackCongr hff).app (A.piece n)).hom)

/-- **The composition law, stated for a named composite.** For `q : T' ⟶ T`, `g : T ⟶ S` and a
morphism `π : T' ⟶ S` together with an identification `q ≫ g = π`, base changing along `g` and
then along `q` agrees with base changing along `π`. -/
def baseAlgebraCompHomOf (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S) (hπ : q ≫ g = π) :
    UnitalHom (baseAlgebra q (baseAlgebra g A)) (baseAlgebra π A) :=
  (baseAlgebraCompHom A q g).comp (baseAlgebraCongrHom A hπ)

/-- **The components of the composition law are the canonical comparison of an iterated inverse
image**, `Stacks.AlgebraicGeometry.ModuleLimits.canHom`. -/
@[simp] theorem baseAlgebraCompHomOf_app (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S) (hπ : q ≫ g = π)
    (n : ℤ) :
    (baseAlgebraCompHomOf A q g π hπ).app n =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom q g π hπ (A.piece n) := rfl

/-- Every component of the composition law at a named composite is an isomorphism. -/
instance isIso_baseAlgebraCompHomOf_app (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S) (hπ : q ≫ g = π)
    (n : ℤ) : IsIso ((baseAlgebraCompHomOf A q g π hπ).app n) :=
  Stacks.AlgebraicGeometry.ModuleLimits.isIso_canHom q g π hπ (A.piece n)

/-- At the composite written out, the named-composite form is the composition law itself. -/
theorem baseAlgebraCompHomOf_rfl (q : T' ⟶ T) (g : T ⟶ S) :
    baseAlgebraCompHomOf A q g (q ≫ g) rfl = baseAlgebraCompHom A q g :=
  UnitalHom.ext fun n =>
    (Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl q g (A.piece n)).trans
      (baseAlgebraCompHom_app A q g n).symm

/-- **The inverse of the composition law at a named composite.** -/
def baseAlgebraCompHomOfInv (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S) (hπ : q ≫ g = π) :
    UnitalHom (baseAlgebra π A) (baseAlgebra q (baseAlgebra g A)) :=
  (baseAlgebraCompHomOf A q g π hπ).inverse

/-- The component in degree `n` of the inverse of the composition law at a named composite is the
inverse of the corresponding component of `baseAlgebraCompHomOf A q g π hπ`. -/
@[simp] theorem baseAlgebraCompHomOfInv_app (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S)
    (hπ : q ≫ g = π) (n : ℤ) :
    (baseAlgebraCompHomOfInv A q g π hπ).app n = inv ((baseAlgebraCompHomOf A q g π hπ).app n) :=
  rfl

/-- Every component of the inverse of the composition law at a named composite is an
isomorphism. -/
instance isIso_baseAlgebraCompHomOfInv_app (q : T' ⟶ T) (g : T ⟶ S) (π : T' ⟶ S)
    (hπ : q ≫ g = π) (n : ℤ) : IsIso ((baseAlgebraCompHomOfInv A q g π hπ).app n) :=
  inferInstanceAs (IsIso (inv ((baseAlgebraCompHomOf A q g π hπ).app n)))

/-! ### The two coherences -/

/-- **The identity coherence in the inner variable, `map_id`.** Base changing along `𝟙 T` after
base changing along `g` is the canonical identification of the inverse image along `𝟙 T` with the
identity: the component in degree `n` is
`AlgebraicGeometry.Scheme.Modules.pullbackId` at the degree-`n` piece of `g^*𝒜`. This is the
right unitality of the inverse-image pseudofunctor. -/
theorem baseAlgebraCompHomOf_id_left_app (g : T ⟶ S) (n : ℤ) :
    (baseAlgebraCompHomOf A (𝟙 T) g g (Category.id_comp g)).app n =
      (Scheme.Modules.pullbackId T).hom.app ((baseAlgebra g A).piece n) :=
  AlgebraicGeometry.pullbackComp_hom_app_comp_pullbackCongr_hom_app g (A.piece n)
    (Category.id_comp g)

/-- **The identity coherence in the outer variable.** Base changing along `𝟙 S` and then along
`q` is the inverse image along `q` of the canonical identification of the inverse image along
`𝟙 S` with the identity. This is the left unitality of the inverse-image pseudofunctor. -/
theorem baseAlgebraCompHomOf_id_right_app (q : T ⟶ S) (n : ℤ) :
    (baseAlgebraCompHomOf A q (𝟙 S) q (Category.comp_id q)).app n =
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId S).hom.app (A.piece n)) :=
  (Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_map_pullbackId_hom_app q (A.piece n)).symm

/-- **The cocycle condition, `map_comp`.** For a chain `T'' ⟶ T' ⟶ T ⟶ S` of morphisms of
schemes the two ways of comparing the thrice base-changed algebra with the base change along the
total composite agree, as unital homomorphisms of sheaves of graded algebras: contracting the
inner pair first and then the outer one, or the outer pair first and then the inner one.

The four hypotheses name the composites; `hrt` is a consequence of the other three and is taken
as a hypothesis so that both sides can be written with the named composites, exactly as in
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`, which is the degreewise content. -/
theorem baseAlgebraCompHomOf_cocycle {T'' : Scheme.{u}} (r : T'' ⟶ T') (q : T' ⟶ T) (g : T ⟶ S)
    (s : T'' ⟶ T) (π : T' ⟶ S) (t : T'' ⟶ S) (hs : r ≫ q = s) (hπ : q ≫ g = π)
    (ht : s ≫ g = t) (hrt : r ≫ π = t) :
    (baseAlgebraMapHom r (baseAlgebraCompHomOf A q g π hπ)).comp
        (baseAlgebraCompHomOf A r π t hrt) =
      (baseAlgebraCompHomOf (baseAlgebra g A) r q s hs).comp
        (baseAlgebraCompHomOf A s g t ht) :=
  UnitalHom.ext fun n =>
    Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp r q g s π t hs hπ ht hrt (A.piece n)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
