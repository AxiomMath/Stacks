module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistUnique
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap

/-!
# Tag 07ZG: transporting `θ` along a change of algebras

Let `ψ : A ⟶ B` on `S` and `ψ' : A' ⟶ B'` on `S'` be homomorphisms of quasi-coherent graded
algebras, `g : S' ⟶ S`, and suppose `A'`, `B'` are identified with `g^*A`, `g^*B` compatibly with
`ψ` and `ψ'`. Given morphisms `c_A`, `c_B` of the relative Projs over `g`, identifications `χ_A`,
`χ_B` of the inverse images of the twists with the twists which carry the homogeneous-section maps
`ψ` to `ψ`, and a morphism `k : U(ψ') ⟶ U(ψ)` over `c_A` and `c_B`, the map `θ_{ψ'}` of Tag 07ZG is
the inverse image `k^*θ_ψ` read through these identifications. This is the compatibility of `θ`
with base change, in the generality in which the base change of a relative Proj is given only up to
the identifications of Stacks 084B.

The proof is the uniqueness of `θ` by condition (1)
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.eq_relativeTwistAlgebraHom_of_mapsPsi`): condition (1)
for the transported map is an equality of two morphisms of sheaves out of `A'_d = g^*A_d`
(`psiLeft`, `psiRight`), which is checked on the sections pulled back from `S`, where it is a
chase through the nine factors of the transport.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.psiLeft`, `…psiRight`: the two sides of condition (1) as
  morphisms of sheaves on the base.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom`: the transport of a map of graded
  algebras on the twists over `U(ψ)` to `U(ψ')`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom_relativeTwistAlgebraHom`: the transport
  of `θ_ψ` is `θ_{ψ'}`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (twD Otw psiU)

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- The source side of condition (1) as a morphism of sheaves on the base. -/
def psiLeft (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (d : ℕ) :
    A.piece (d : ℤ) ⟶ (Scheme.Modules.pushforward (relativeMapHom ψ ≫ (relativeProj A).toBase)).obj
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d)) :=
  (twD A).ψ d ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (relativeMapHom ψ)).unit.app
        (relativeTwist A d) ≫
      (Scheme.Modules.pushforward (relativeMapHom ψ)).map (θ'.app d)) ≫
    (Scheme.Modules.pushforwardComp (relativeMapHom ψ) (relativeProj A).toBase).hom.app _

/-- The target side of condition (1) as a morphism of sheaves on the base. -/
def psiRight (d : ℕ) :
    A.piece (d : ℤ) ⟶ (Scheme.Modules.pushforward (relativeMapHom ψ ≫ (relativeProj A).toBase)).obj
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d)) :=
  ψ.app d ≫ (twD B).ψ d ≫ (Scheme.Modules.pushforward (relativeProj B).toBase).map
    ((Scheme.Modules.pullbackPushforwardAdjunction ψ.relativeMapDomain.ι).unit.app
      (relativeTwist B d)) ≫
    (Scheme.Modules.pushforwardComp ψ.relativeMapDomain.ι (relativeProj B).toBase).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (relativeMapHom_comp_toBase ψ).symm).hom.app _

/-- `psiLeft ψ θ' d` on a section `a` over `V`: `θ'` applied to the inverse image along
`relativeMapHom ψ` of the homogeneous section `psiU A d V a`. -/
theorem psiLeft_app (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    (psiLeft ψ θ' d).val.app (op V) a =
      (θ'.app (d : ℤ)).val.app (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl (psiU A d V a)) := by
  unfold Scheme.Modules.pullbackSection
  exact (congrArg ((θ'.app (d : ℤ)).val.app _)
    (PresheafOfModules.map_id_apply
      ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A d)).val
      (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))) _)).symm

/-- `psiRight ψ d` on a section `a` over `V`: the inverse image along the inclusion of `U(ψ)` of
the homogeneous section `psiU B d V (ψ a)`. -/
theorem psiRight_app (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    (psiRight ψ d).val.app (op V) a =
      Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B d)
        ((relativeProj B).toBase ⁻¹ᵁ V) _ (relativeMapHom_preimage_toBase ψ V).le
        (psiU B d V ((ψ.app (d : ℤ)).app V a)) := by
  rfl

/-- Condition (1), from the equality of the two morphisms on the base. -/
theorem mapsPsi_of_psiLeft_eq {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))} (h : ∀ d, psiLeft ψ θ' d = psiRight ψ d) : MapsPsi ψ θ' :=
  fun d V a => (psiLeft_app ψ θ' d V a).symm.trans
    ((congrArg (fun φ => φ.val.app (op V) a) (h d)).trans (psiRight_app ψ d V a))

/-- The inverse of the pseudofunctoriality isomorphism on a section pulled back along a
composite. -/
theorem pullbackComp_inv_pullbackSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U)
    (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (Scheme.Modules.pullbackSection (f ≫ g) M U V h a) =
      Scheme.Modules.pullbackSection f ((Scheme.Modules.pullback g).obj M) W V hf
        (Scheme.Modules.pullbackSection g M U W hg a) := by
  rw [← Scheme.Modules.pullbackSection_comp f g M U W V hg hf h a]
  exact congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op V) _)
    ((Scheme.Modules.pullbackComp f g).hom_inv_id_app M) |>.trans rfl

section BaseChange

open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

variable {S' : Scheme.{u}} (g : S' ⟶ S) {A' B' : SheafGradedAlgebra S'}
  (ψ' : SheafGradedAlgebraHom A' B')
  {cA : (relativeProj A').scheme ⟶ (relativeProj A).scheme}
  {cB : (relativeProj B').scheme ⟶ (relativeProj B).scheme}
  (χA : Stacks.RingedSpace.pullbackGradedAlgebra cA.toLRSHom.toShHom (twistAlgebra A) ≅
    twistAlgebra A')
  (χB : Stacks.RingedSpace.pullbackGradedAlgebra cB.toLRSHom.toShHom (twistAlgebra B) ≅
    twistAlgebra B')
  (k : ψ'.relativeMapDomain.toScheme ⟶ ψ.relativeMapDomain.toScheme)
  (hr : relativeMapHom ψ' ≫ cA = k ≫ relativeMapHom ψ)
  (hι : k ≫ ψ.relativeMapDomain.ι = ψ'.relativeMapDomain.ι ≫ cB)

/-- **A map of graded algebras on the twists over `U(ψ)`, transported to `U(ψ')`** along a
morphism `k : U(ψ') ⟶ U(ψ)` lying over morphisms `c_A`, `c_B` of the relative Projs and
identifications `χ_A`, `χ_B` of the inverse images of the twists: the inverse image `k^*θ`, read
through the pseudofunctoriality of the inverse image and `χ_A`, `χ_B`. -/
def transportTwistHom (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) :
    SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ').toLRSHom.toShHom
        (twistAlgebra A'))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ'.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B')) :=
  (Stacks.RingedSpace.pullbackGradedAlgebraMapIso (relativeMapHom ψ').toLRSHom.toShHom χA).inv ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra A) (relativeMapHom ψ') cA).hom ≫
    (pullbackGradedAlgebraCongrIso (twistAlgebra A) hr).hom ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra A) k (relativeMapHom ψ)).inv ≫
    Stacks.RingedSpace.pullbackGradedAlgebraMap k.toLRSHom.toShHom θ ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra B) k ψ.relativeMapDomain.ι).hom ≫
    (pullbackGradedAlgebraCongrIso (twistAlgebra B) hι).hom ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra B) ψ'.relativeMapDomain.ι cB).inv ≫
    Stacks.RingedSpace.pullbackGradedAlgebraMap ψ'.relativeMapDomain.ι.toLRSHom.toShHom χB.hom

/-- The value of a composite of morphisms of modules on a section. -/
theorem val_app_comp_apply {X : Scheme.{u}} {M N K : X.Modules} (f : M ⟶ N) (h : N ⟶ K)
    (O : X.Opens) (x : M.val.obj (op O)) :
    (f ≫ h).val.app (op O) x = h.val.app (op O) (f.val.app (op O) x) := rfl

/-- `transportTwistHom` in degree `n`, on sections: the nine factors applied in turn. -/
theorem transportTwistHom_app_apply (θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) (n : ℤ) (O : ψ'.relativeMapDomain.toScheme.Opens) (x) :
    ((transportTwistHom ψ ψ' χA χB k hr hι θ).app n).val.app (op O) x =
      ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map (χB.hom.app n)).val.app (op O)
      (((Scheme.Modules.pullbackComp ψ'.relativeMapDomain.ι cB).inv.app
        ((twistAlgebra B).piece n)).val.app (op O)
      (((Scheme.Modules.pullbackCongr hι).hom.app ((twistAlgebra B).piece n)).val.app (op O)
      (((Scheme.Modules.pullbackComp k ψ.relativeMapDomain.ι).hom.app
        ((twistAlgebra B).piece n)).val.app (op O)
      (((Scheme.Modules.pullback k).map (θ.app n)).val.app (op O)
      (((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op O)
      (((Scheme.Modules.pullbackCongr hr).hom.app ((twistAlgebra A).piece n)).val.app (op O)
      (((Scheme.Modules.pullbackComp (relativeMapHom ψ') cA).hom.app
        ((twistAlgebra A).piece n)).val.app (op O)
      (((Scheme.Modules.pullback (relativeMapHom ψ')).map (χA.inv.app n)).val.app (op O)
        x)))))))) :=
  rfl

/-- The first four factors of `transportTwistHom`, on a section pulled back along `c_A` and then
`r_{ψ'}`: the section pulled back along `r_ψ` and then `k`. -/
theorem transportTwistHom_source (n : ℤ) {Y : (relativeProj A).scheme.Opens}
    {Y' : (relativeProj A').scheme.Opens} {W : ψ'.relativeMapDomain.toScheme.Opens}
    (hY : Y' ≤ cA ⁻¹ᵁ Y) (hW : W ≤ relativeMapHom ψ' ⁻¹ᵁ Y')
    (h2 : W ≤ (relativeMapHom ψ' ≫ cA) ⁻¹ᵁ Y) (h3 : W ≤ k ⁻¹ᵁ (relativeMapHom ψ ⁻¹ᵁ Y))
    (h3' : W ≤ (k ≫ relativeMapHom ψ) ⁻¹ᵁ Y) (m : Γ(relativeTwist A n, Y)) :
    ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hr).hom.app ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackComp (relativeMapHom ψ') cA).hom.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullback (relativeMapHom ψ')).map (χA.inv.app n)).val.app (op W)
        (Scheme.Modules.pullbackSection (relativeMapHom ψ') (relativeTwist A' n) Y' W hW
          ((χA.hom.app n).val.app (op Y')
            (Scheme.Modules.pullbackSection cA (relativeTwist A n) Y Y' hY m)))))) =
      Scheme.Modules.pullbackSection k
        ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n)) _ W h3
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) Y _ le_rfl m) := by
  have e : χA.hom.app n ≫ χA.inv.app n = 𝟙 _ :=
    congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n) χA.hom_inv_id
  have s1 := congrArg (fun φ => φ.val.app (op W) (Scheme.Modules.pullbackSection
      (relativeMapHom ψ') ((Scheme.Modules.pullback cA).obj (relativeTwist A n)) Y' W hW
      (Scheme.Modules.pullbackSection cA (relativeTwist A n) Y Y' hY m)))
    (((Scheme.Modules.pullback (relativeMapHom ψ')).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback (relativeMapHom ψ')).map e).trans
        ((Scheme.Modules.pullback (relativeMapHom ψ')).map_id _)))
  have s0 := Scheme.Modules.pullbackSection_naturality (relativeMapHom ψ') (χA.hom.app n) Y' W hW
    (Scheme.Modules.pullbackSection cA (relativeTwist A n) Y Y' hY m)
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hr).hom.app ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackComp (relativeMapHom ψ') cA).hom.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullback (relativeMapHom ψ')).map (χA.inv.app n)).val.app (op W) z))))
    s0.symm).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hr).hom.app ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackComp (relativeMapHom ψ') cA).hom.app
        ((twistAlgebra A).piece n)).val.app (op W) z))) s1).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hr).hom.app ((twistAlgebra A).piece n)).val.app (op W) z))
    (Scheme.Modules.pullbackSection_comp _ _ _ _ _ _ hY hW h2 m)).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
        ((twistAlgebra A).piece n)).val.app (op W) z)
    (Scheme.Modules.pullbackSection_congr hr _ _ _ h2 h3' m)).trans ?_
  exact pullbackComp_inv_pullbackSection _ _ _ _ _ _ le_rfl h3 h3' m

/-- The last four factors of `transportTwistHom`, on a section pulled back along `ι` and then
`k`: the section pulled back along `c_B`, read through `χ_B`, and pulled back along `ι'`. -/
theorem transportTwistHom_target (n : ℤ) {Z : (relativeProj B).scheme.Opens}
    {Z' : (relativeProj B').scheme.Opens} {Y : ψ.relativeMapDomain.toScheme.Opens}
    {W : ψ'.relativeMapDomain.toScheme.Opens}
    (hZ : Z' ≤ cB ⁻¹ᵁ Z) (hY : Y ≤ ψ.relativeMapDomain.ι ⁻¹ᵁ Z) (hW : W ≤ k ⁻¹ᵁ Y)
    (h6' : W ≤ (k ≫ ψ.relativeMapDomain.ι) ⁻¹ᵁ Z)
    (h7 : W ≤ (ψ'.relativeMapDomain.ι ≫ cB) ⁻¹ᵁ Z) (h8 : W ≤ ψ'.relativeMapDomain.ι ⁻¹ᵁ Z')
    (b : Γ(relativeTwist B n, Z)) :
    ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map (χB.hom.app n)).val.app (op W)
      (((Scheme.Modules.pullbackComp ψ'.relativeMapDomain.ι cB).inv.app
        ((twistAlgebra B).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hι).hom.app ((twistAlgebra B).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackComp k ψ.relativeMapDomain.ι).hom.app
        ((twistAlgebra B).piece n)).val.app (op W)
        (Scheme.Modules.pullbackSection k
          ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)) Y W hW
          (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B n) Z Y hY b))))) =
      Scheme.Modules.pullbackSection ψ'.relativeMapDomain.ι (relativeTwist B' n) Z' W h8
        ((χB.hom.app n).val.app (op Z')
          (Scheme.Modules.pullbackSection cB (relativeTwist B n) Z Z' hZ b)) := by
  refine (congrArg (fun z => ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map
        (χB.hom.app n)).val.app (op W)
      (((Scheme.Modules.pullbackComp ψ'.relativeMapDomain.ι cB).inv.app
        ((twistAlgebra B).piece n)).val.app (op W)
      (((Scheme.Modules.pullbackCongr hι).hom.app ((twistAlgebra B).piece n)).val.app (op W) z)))
    (Scheme.Modules.pullbackSection_comp _ _ _ _ _ _ hY hW h6' b)).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map
        (χB.hom.app n)).val.app (op W)
      (((Scheme.Modules.pullbackComp ψ'.relativeMapDomain.ι cB).inv.app
        ((twistAlgebra B).piece n)).val.app (op W) z))
    (Scheme.Modules.pullbackSection_congr hι _ _ _ h6' h7 b)).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map
        (χB.hom.app n)).val.app (op W) z)
    (pullbackComp_inv_pullbackSection _ _ _ _ _ _ hZ h8 h7 b)).trans ?_
  exact Scheme.Modules.pullbackSection_naturality _ (χB.hom.app n) _ W h8 _

/-- Preimages of an open of the base agree along a commutative square of schemes. -/
private theorem preimage_comm_eq {X Y Z T : Scheme.{u}} {c : X ⟶ Y} {f : Y ⟶ T} {f' : X ⟶ Z}
    {g : Z ⟶ T} (h : c ≫ f = f' ≫ g) (U : T.Opens) : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = c ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]

/-- **The chase behind the base change of `θ`**: on the inverse image along `r_{ψ'}` of the section
`ψ_{A'}(ε_A(g^*a))`, the transport of `θ_ψ` is the inverse image along the inclusion of `U(ψ')` of
`ψ_{B'}(ε_B(g^*ψ(a)))`. -/
theorem transportTwistHom_app_pullbackSection_psiU
    (hcA : cA ≫ (relativeProj A).toBase = (relativeProj A').toBase ≫ g)
    (hcB : cB ≫ (relativeProj B).toBase = (relativeProj B').toBase ≫ g)
    (εA : ∀ d : ℕ, (Scheme.Modules.pullback g).obj (A.piece (d : ℤ)) ≅ A'.piece (d : ℤ))
    (εB : ∀ d : ℕ, (Scheme.Modules.pullback g).obj (B.piece (d : ℤ)) ≅ B'.piece (d : ℤ))
    (hχA : ∀ (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V))
      (hV : (relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ cA ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)),
      (χA.hom.app (d : ℤ)).val.app (op ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ V)))
          (Scheme.Modules.pullbackSection cA (relativeTwist A d) _ _ hV (psiU A d V a)) =
        psiU A' d (g ⁻¹ᵁ V) ((εA d).hom.val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (A.piece (d : ℤ)) V _ le_rfl a)))
    (hχB : ∀ (d : ℕ) (V : S.Opens) (b : Γ(B.piece (d : ℤ), V))
      (hV : (relativeProj B').toBase ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ cB ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V)),
      (χB.hom.app (d : ℤ)).val.app (op ((relativeProj B').toBase ⁻¹ᵁ (g ⁻¹ᵁ V)))
          (Scheme.Modules.pullbackSection cB (relativeTwist B d) _ _ hV (psiU B d V b)) =
        psiU B' d (g ⁻¹ᵁ V) ((εB d).hom.val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (B.piece (d : ℤ)) V _ le_rfl b)))
    (d : ℕ) (U : S.Opens) (a : Γ(A.piece (d : ℤ), U)) :
    ((transportTwistHom ψ ψ' χA χB k hr hι (relativeTwistAlgebraHom ψ)).app (d : ℤ)).val.app
        (op (relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U))))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ') (relativeTwist A' d) _ _ le_rfl
          (psiU A' d (g ⁻¹ᵁ U) ((εA d).hom.val.app (op (g ⁻¹ᵁ U))
            (Scheme.Modules.pullbackSection g (A.piece (d : ℤ)) U _ le_rfl a)))) =
      Scheme.Modules.pullbackSection ψ'.relativeMapDomain.ι (relativeTwist B' d) _ _
        (relativeMapHom_preimage_toBase ψ' (g ⁻¹ᵁ U)).le
        (psiU B' d (g ⁻¹ᵁ U) ((εB d).hom.val.app (op (g ⁻¹ᵁ U))
          (Scheme.Modules.pullbackSection g (B.piece (d : ℤ)) U _ le_rfl
            ((ψ.app (d : ℤ)).app U a)))) := by
  have hV := (preimage_comm_eq hcA U).le
  have hVB := (preimage_comm_eq hcB U).le
  have h2 : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      (relativeMapHom ψ' ≫ cA) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) := by
    rw [Scheme.Hom.comp_preimage]
    exact (relativeMapHom ψ').preimage_mono hV
  have h3 : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      k ⁻¹ᵁ (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) :=
    h2.trans ((congrArg (fun f => f ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) hr).trans
      (Scheme.Hom.comp_preimage _ _ _)).le
  have h3' : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      (k ≫ relativeMapHom ψ) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) :=
    h2.trans (congrArg (fun f => f ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U)) hr).le
  have h5 := (relativeMapHom_preimage_toBase ψ U).le
  have h6 : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      k ⁻¹ᵁ (ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U)) :=
    h3.trans (k.preimage_mono h5)
  have h6' : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      (k ≫ ψ.relativeMapDomain.ι) ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U) :=
    h6.trans (Scheme.Hom.comp_preimage _ _ _).ge
  have h8 := (relativeMapHom_preimage_toBase ψ' (g ⁻¹ᵁ U)).le
  have h7 : relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U)) ≤
      (ψ'.relativeMapDomain.ι ≫ cB) ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ U) := by
    rw [Scheme.Hom.comp_preimage]
    exact h8.trans (ψ'.relativeMapDomain.ι.preimage_mono hVB)
  let W := relativeMapHom ψ' ⁻¹ᵁ ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ U))
  let F1 := ((Scheme.Modules.pullback (relativeMapHom ψ')).map (χA.inv.app (d : ℤ))).val.app (op W)
  let F2 := ((Scheme.Modules.pullbackComp (relativeMapHom ψ') cA).hom.app
    (relativeTwist A d)).val.app (op W)
  let F3 := ((Scheme.Modules.pullbackCongr hr).hom.app (relativeTwist A d)).val.app (op W)
  let F4 := ((Scheme.Modules.pullbackComp k (relativeMapHom ψ)).inv.app
    (relativeTwist A d)).val.app (op W)
  let F5 := ((Scheme.Modules.pullback k).map ((relativeTwistAlgebraHom ψ).app (d : ℤ))).val.app
    (op W)
  let F6 := ((Scheme.Modules.pullbackComp k ψ.relativeMapDomain.ι).hom.app
    (relativeTwist B d)).val.app (op W)
  let F7 := ((Scheme.Modules.pullbackCongr hι).hom.app (relativeTwist B d)).val.app (op W)
  let F8 := ((Scheme.Modules.pullbackComp ψ'.relativeMapDomain.ι cB).inv.app
    (relativeTwist B d)).val.app (op W)
  let F9 := ((Scheme.Modules.pullback ψ'.relativeMapDomain.ι).map (χB.hom.app (d : ℤ))).val.app
    (op W)
  have s5 : F5 (Scheme.Modules.pullbackSection k
        ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A d)) _ W h3
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A d) _ _ le_rfl
          (psiU A d U a))) =
      Scheme.Modules.pullbackSection k
        ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B d)) _ W h3
        (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B d) _ _ h5
          (psiU B d U ((ψ.app (d : ℤ)).app U a))) :=
    (Scheme.Modules.pullbackSection_naturality k ((relativeTwistAlgebraHom ψ).app (d : ℤ))
      _ W h3 _).trans (congrArg (Scheme.Modules.pullbackSection k _ _ W h3)
        (mapsPsi_relativeTwistAlgebraHom ψ d U a))
  refine (transportTwistHom_app_apply ψ ψ' χA χB k hr hι _ (d : ℤ) W _).trans ?_
  refine (congrArg (fun z => F9 (F8 (F7 (F6 (F5 (F4 (F3 (F2 (F1
    (Scheme.Modules.pullbackSection (relativeMapHom ψ') (relativeTwist A' d) _ W le_rfl z))))))))))
    (hχA d U a hV).symm).trans ?_
  refine (congrArg (fun z => F9 (F8 (F7 (F6 (F5 z)))))
    (transportTwistHom_source ψ ψ' χA k hr (d : ℤ) hV le_rfl h2 h3 h3' (psiU A d U a))).trans ?_
  refine (congrArg (fun z => F9 (F8 (F7 (F6 z)))) s5).trans ?_
  refine (transportTwistHom_target ψ ψ' χB k hι (d : ℤ) hVB h5 h3 h6' h7 h8 _).trans ?_
  exact congrArg (Scheme.Modules.pullbackSection ψ'.relativeMapDomain.ι (relativeTwist B' d) _ W h8)
    (hχB d U _ hVB)

/-- **The map `θ` of Tag 07ZG is compatible with base change.** Let `g : S' ⟶ S`, `ψ : A ⟶ B` on
`S` and `ψ' : A' ⟶ B'` on `S'`, with `A'`, `B'` identified with `g^*A`, `g^*B` by `ε_A`, `ε_B`
compatibly with `ψ` and `ψ'`. Let `c_A`, `c_B` be morphisms of the relative Projs over `g` and
`χ_A`, `χ_B` identifications of the inverse images of the twists carrying `ψ` to `ψ`, and
`k : U(ψ') ⟶ U(ψ)` a morphism over `c_A` and `c_B`. Then `θ_{ψ'}` is `k^*θ_ψ`, transported. -/
theorem transportTwistHom_relativeTwistAlgebraHom
    (hcA : cA ≫ (relativeProj A).toBase = (relativeProj A').toBase ≫ g)
    (hcB : cB ≫ (relativeProj B).toBase = (relativeProj B').toBase ≫ g)
    (εA : ∀ d : ℕ, (Scheme.Modules.pullback g).obj (A.piece (d : ℤ)) ≅ A'.piece (d : ℤ))
    (εB : ∀ d : ℕ, (Scheme.Modules.pullback g).obj (B.piece (d : ℤ)) ≅ B'.piece (d : ℤ))
    (hψ' : ∀ d : ℕ, (εA d).hom ≫ ψ'.app (d : ℤ) =
      (Scheme.Modules.pullback g).map (ψ.app (d : ℤ)) ≫ (εB d).hom)
    (hχA : ∀ (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V))
      (hV : (relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ cA ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)),
      (χA.hom.app (d : ℤ)).val.app (op ((relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ V)))
          (Scheme.Modules.pullbackSection cA (relativeTwist A d) _ _ hV (psiU A d V a)) =
        psiU A' d (g ⁻¹ᵁ V) ((εA d).hom.val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (A.piece (d : ℤ)) V _ le_rfl a)))
    (hχB : ∀ (d : ℕ) (V : S.Opens) (b : Γ(B.piece (d : ℤ), V))
      (hV : (relativeProj B').toBase ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ cB ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V)),
      (χB.hom.app (d : ℤ)).val.app (op ((relativeProj B').toBase ⁻¹ᵁ (g ⁻¹ᵁ V)))
          (Scheme.Modules.pullbackSection cB (relativeTwist B d) _ _ hV (psiU B d V b)) =
        psiU B' d (g ⁻¹ᵁ V) ((εB d).hom.val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (B.piece (d : ℤ)) V _ le_rfl b))) :
    transportTwistHom ψ ψ' χA χB k hr hι (relativeTwistAlgebraHom ψ) =
      relativeTwistAlgebraHom ψ' := by
  refine eq_relativeTwistAlgebraHom_of_mapsPsi ψ' (mapsPsi_of_psiLeft_eq ψ' fun d => ?_)
  refine (cancel_epi (εA d).hom).mp ?_
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection g fun U a => ?_
  have hψa : (ψ'.app (d : ℤ)).val.app (op (g ⁻¹ᵁ U)) ((εA d).hom.val.app (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (A.piece (d : ℤ)) U _ le_rfl a)) =
      (εB d).hom.val.app (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (B.piece (d : ℤ)) U _ le_rfl
          ((ψ.app (d : ℤ)).app U a)) :=
    (congrArg (fun φ => φ.val.app (op (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackSection g (A.piece (d : ℤ)) U _ le_rfl a)) (hψ' d)).trans
      (congrArg ((εB d).hom.val.app (op (g ⁻¹ᵁ U)))
        (Scheme.Modules.pullbackSection_naturality g (ψ.app (d : ℤ)) U _ le_rfl a))
  refine (val_app_comp_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (val_app_comp_apply _ _ _ _).symm
  refine (psiLeft_app ψ' _ d (g ⁻¹ᵁ U) _).trans ?_
  refine Eq.trans ?_ (psiRight_app ψ' d (g ⁻¹ᵁ U) _).symm
  refine (transportTwistHom_app_pullbackSection_psiU ψ g ψ' χA χB k hr hι hcA hcB εA εB hχA hχB
    d U a).trans ?_
  exact congrArg (fun z => Scheme.Modules.pullbackSection ψ'.relativeMapDomain.ι
    (relativeTwist B' d) _ _ (relativeMapHom_preimage_toBase ψ' (g ⁻¹ᵁ U)).le
    (psiU B' d (g ⁻¹ᵁ U) z)) hψa.symm

end BaseChange



end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
