module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology
public import StacksFrontier.Deformation.Artin.Obstruction.InfAutBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory

/-!
# Fibres of the functoriality map of a naive obstruction theory

Let `𝒳` be a category fibred in groupoids over the big fppf site of a base scheme `S` which
satisfies (RS*) and carries a naive obstruction theory (Stacks 07YP). For a ring map `A ⟶ B`
in the site and the restriction `y = x|_{Spec B}` of an object `x` of `𝒳` over `Spec A` there
is a functoriality map `E_x ⟶ E_y`, and Stacks 07YT asserts that for every `B`-algebra `k`
which is a field this map induces bijections

`H^i(E_x ⊗ᴸ_A k) ⟶ H^i(E_y ⊗ᴸ_B k)` for `i = 0, 1`.

The source proof has two steps. First, (RS*) identifies the lifts of `x` over `A[k]` and the
lifts of `y` over `B[k]` with the lifts of `z = x|_{Spec k}` over `k[k]`, because
`A[k] = A ×_k k[k]` and `B[k] = B ×_k k[k]`, so the properties of a naive obstruction theory
force the functoriality map to induce bijections `Ext^i_A(E_x, k) ⟶ Ext^i_B(E_y, k)` for
`i = -1, 0`. Second, by Stacks 07YK those Ext groups are the `k`-linear duals of
`H^{-i}(E_x ⊗ᴸ_A k)` and `H^{-i}(E_y ⊗ᴸ_B k)`, so the two displayed maps have bijective duals
and are therefore bijective.

Both steps are carried out here, so this file proves Stacks 07YT in full. The first step
splits into the identification `Lift(x, A[k]) = Lift(y, B[k])` of isomorphism classes of
lifts, which is `Deformation.Artin.bijective_squareZeroLiftBaseChangeMap` and gives the
bijectivity on `Ext^0` through clauses (2) and (iii) of Stacks 07YP, and the same
identification on the automorphisms of the trivial lift, which is
`Deformation.Artin.bijective_of_isInfinitesimalAutomorphismBaseChange` and gives the
bijectivity on `Ext^{-1}`. The second step is the duality of Stacks 07YK.

## Main results

* `Deformation.Artin.bijective_hom_of_precomp_dual_bijective`: a morphism of `k`-modules whose
  precomposition action on maps into `k` is bijective is itself bijective. This is the
  "isomorphisms on dual vector spaces hence isomorphisms" step of the source proof.
* `Deformation.Artin.homologyMap_bijective_of_extIntoFieldRestriction_bijective`: the reduction
  lemma. If pullback of Ext classes with field coefficient along a morphism
  `E ⟶ Res_A^B F` is bijective in degree `j`, then the induced map
  `H^{-j}(E ⊗ᴸ_A k) ⟶ H^{-j}(F ⊗ᴸ_B k)` is bijective. This is the Stacks 07YK step, and it
  exhibits the Ext bijectivity as the only input the conclusion of Stacks 07YT needs.
* `Deformation.Artin.NaiveObstructionTheory.functoriality_homology_bijective`:
  **Stacks 07YT**, with no hypothesis beyond the two site conditions on the coefficient field:
  the functoriality map of a naive obstruction theory induces bijections
  `H^i(E_x ⊗ᴸ_A k) ⟶ H^i(E_y ⊗ᴸ_B k)` for `i = 0` and `i = 1`.

## Implementation notes

The duality of Stacks 07YK is
`Deformation.Artin.extIntoFieldEquivDualBaseChangeHomology`, which identifies
`Ext^j_A(E, k)` with the `k`-linear dual of `H^{-j}(E ⊗ᴸ_A k)`; its naturality in the source
ring, `Deformation.Artin.extIntoFieldEquivDualBaseChangeHomology_restrictScalars`, identifies
pullback of Ext classes along `E ⟶ Res_A^B F` with precomposition by the induced map
`Deformation.Artin.derivedBaseChangeMap` of derived base changes. Composing with that
identification on both sides turns the Ext bijectivity into bijectivity of precomposition,
which `bijective_hom_of_precomp_dual_bijective` converts into bijectivity of the map itself.
The homological degree and the Ext degree are related by `i = -j`; they are carried as two
parameters with that equation rather than by substituting `-j`, which keeps the statement free
of `eqToHom` transports between the two homology functors.

The coefficient field appears as `ULift k` because the duality lemmas state `Ext` into the
`ULift` of `k` in the common module universe; `ULift.moduleEquiv` is used to pass between
`Hom(V, ULift k)` and the honest dual `V →ₗ[k] k`, where Mathlib's
`LinearMap.dualMap_bijective_iff` applies. No finite dimensionality is needed.

`NaiveObstructionTheory.functoriality_homology_bijective` is read off the chain of
`StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology`, which assembles the two steps
from the two Rim–Schlessinger inputs, rather than from the reduction lemma of this file.
Its two hypotheses `hM` and `hN` say that the two module structures which the ring maps
`A ⟶ k` and `B ⟶ k` put on `k` occur in the chosen big site; they are needed because the
tangent and infinitesimal-automorphism functors of Stacks 07Y9 are defined only on site
modules, they are satisfiable by taking the site large enough, and the definition of a naive
obstruction theory already carries a hypothesis of this kind in its condition (iv). They
assume no mathematical statement.

The Rim–Schlessinger input on infinitesimal automorphisms is
`StacksFrontier.Deformation.Artin.Obstruction.InfAutBaseChange`, where the transition of
Stacks 07YA on `Inf` is shown to be single-valued — which needs the commutativity of the
infinitesimal automorphisms, the Eckmann–Hilton half of Stacks 06I6 — and bijective.

## References

* [Stacks Project, Tag 07YT](https://stacks.math.columbia.edu/tag/07YT)
* [Stacks Project, Tag 07YP](https://stacks.math.columbia.edu/tag/07YP)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-- A morphism `u : X ⟶ Y` of `k`-modules over a field `k` whose precomposition action
`(Y ⟶ ULift k) → (X ⟶ ULift k)` is bijective is itself bijective. This is the step
"induce isomorphisms on dual vector spaces hence are isomorphisms" of Stacks 07YT. -/
theorem bijective_hom_of_precomp_dual_bijective {k : Type u} [Field k] {X Y : ModuleCat.{u} k}
    (u : X ⟶ Y)
    (hcomp : Function.Bijective (fun α : Y ⟶ ModuleCat.of k (ULift.{u} k) => u ≫ α)) :
    Function.Bijective u.hom := by
  let e (Z : ModuleCat.{u} k) : (Z ⟶ ModuleCat.of k (ULift.{u} k)) ≃ (Z →ₗ[k] k) :=
    { toFun α := (ULift.moduleEquiv (R := k)).toLinearMap ∘ₗ α.hom
      invFun φ := ModuleCat.ofHom ((ULift.moduleEquiv (R := k)).symm.toLinearMap ∘ₗ φ)
      left_inv α := by
        ext
        simp
      right_inv φ := by
        ext
        simp }
  rw [← LinearMap.dualMap_bijective_iff]
  have hfac : (u.hom.dualMap : (Y →ₗ[k] k) → (X →ₗ[k] k)) =
      e X ∘ (fun α => u ≫ α) ∘ (e Y).symm := by
    ext φ x
    simp [e]
  rw [hfac]
  exact (e X).bijective.comp (hcomp.comp (e Y).symm.bijective)

/-- The reduction underlying Stacks 07YT. Let `f : A ⟶ B` be a ring map, `g : B ⟶ k` a ring map
to a field, and `h : E ⟶ Res_A^B F` a morphism of bounded-above derived objects. If pullback of
Ext classes with coefficient `k` along `h` is bijective in degree `j`, then the induced map
`H^{-j}(E ⊗ᴸ_A k) ⟶ H^{-j}(F ⊗ᴸ_B k)` is bijective. By Stacks 07YK the two sides are dual to
one another, so this is exactly the dualisation step of the source proof. -/
theorem homologyMap_bijective_of_extIntoFieldRestriction_bijective {A B k : Type u} [CommRing A]
    [CommRing B] [Field k] (f : A →+* B) (g : B →+* k)
    (E : DerivedCategory.Minus (ModuleCat.{u} A)) (F : DerivedCategory.Minus (ModuleCat.{u} B))
    (h : E.obj ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F.obj) (i j : ℤ)
    (hij : i = -j)
    (hExt : Function.Bijective
      (DerivedCategory.extIntoFieldRestriction.{u, u, u, u} f g E.obj F.obj h j)) :
    Function.Bijective (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
      (DerivedCategory.derivedBaseChangeMap.{u, u, u, u} f g E.obj F.obj h)).hom) := by
  subst hij
  apply bijective_hom_of_precomp_dual_bijective
  have hfac : (fun α : _ ⟶ ModuleCat.of k (ULift.{u} k) =>
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-j)).map
          (DerivedCategory.derivedBaseChangeMap.{u, u, u, u} f g E.obj F.obj h) ≫ α) =
      (DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} (g.comp f) E j) ∘
        (DerivedCategory.extIntoFieldRestriction.{u, u, u, u} f g E.obj F.obj h j) ∘
        (DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} g F j).symm := by
    funext α
    simp only [Function.comp_apply]
    rw [DerivedCategory.extIntoFieldEquivDualBaseChangeHomology_restrictScalars.{u, u, u, u}
      f g E F h j]
    simp
  rw [hfac]
  exact (Equiv.bijective _).comp (hExt.comp (Equiv.bijective _))

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- **Stacks 07YT.** Let `𝒳` be fibred in groupoids over the big fppf site of `S`, satisfying
(RS*) and endowed with a naive obstruction theory. Let `A ⟶ B` be a ring map in the site, let
`y = x|_{Spec B}` be the restriction of an object `x` of `𝒳` over `Spec A`, and let `k` be a
`B`-algebra which is a field whose two module structures occur in the site. Then the
functoriality map `E_x ⟶ E_y` induces bijections
`H^i(E_x ⊗ᴸ_A k) ⟶ H^i(E_y ⊗ᴸ_B k)` for `i = 0` and `i = 1`.

Nothing about the comparison is assumed. The first step of the source proof is the (RS*)
identification of the lifts of `x` over `A[k]` with the lifts of `y` over `B[k]`, on
isomorphism classes by `Deformation.Artin.bijective_squareZeroLiftBaseChangeMap` and on the
automorphisms of the trivial lift by
`Deformation.Artin.bijective_of_isInfinitesimalAutomorphismBaseChange`; through clauses (2)
and (iii) of Stacks 07YP these give bijectivity on `Ext^0` and on `Ext^{-1}`, and the duality
of Stacks 07YK turns that into the conclusion in degrees `0` and `1`. -/
@[stacks 07YT]
theorem NaiveObstructionTheory.functoriality_homology_bijective
    {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp} {c : AffineChart S}
    (N : NaiveObstructionTheory B S hS p hp hRS c) (P Q : ChartedObject B S hS p c)
    (hom : AffineObject.Hom P.obj Q.obj) [Algebra P.ring Q.ring]
    [IsScalarTower c.ring P.ring Q.ring] (halg : algebraMap P.ring Q.ring = hom.alg.ringMap)
    {k : Type u} [Field k] (g : Q.ring →+* k)
    (hM : IsSiteModule P.ring B
      ((ModuleCat.restrictScalars (g.comp (algebraMap P.ring Q.ring))).obj
        (ModuleCat.of k (ULift.{u} k))))
    (hN : IsSiteModule Q.ring B
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k)))) :
    Function.Bijective (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        (naiveObstructionFieldBaseChangeMap N P Q hom halg g)).hom) ∧
      Function.Bijective (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).map
        (naiveObstructionFieldBaseChangeMap N P Q hom halg g)).hom) :=
  bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_infAut N P Q hom halg g
    hM hN (fun σ hσ => bijective_of_isInfinitesimalAutomorphismBaseChange_equiv hp hRS hom
      (algebraMap P.ring Q.ring) halg
      (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
      (bijective_restrictScalarsAddHom_of_isIso (algebraMap P.ring Q.ring) _)
      ((P.infAut hp hRS).autEquiv _) ((Q.infAut hp hRS).autEquiv _) σ hσ)

end Deformation.Artin
