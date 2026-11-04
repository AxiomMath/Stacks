module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeCompHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange

/-!
# The base-change comparison of projective bundles is functorial

Let `q : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and let `E`, `E'`, `E''` be
quasi-coherent modules on `Z`, `Y`, `X` with identifications `c : E' ≅ g^*E`,
`c' : E'' ≅ q^*E'` and `c'' : E'' ≅ (q ≫ g)^*E`.  If the three identifications are compatible —
`c''` is `c'` followed by `q^*c` and the canonical comparison `q^*g^*E ≅ (q ≫ g)^*E` — then the
base-change comparison morphisms of projective bundles satisfy the composition law

`𝐏(E'') ⟶ 𝐏(E') ⟶ 𝐏(E)  =  𝐏(E'') ⟶ 𝐏(E)`.

The composition law for the base change of a relative `Proj`,
`Stacks.RelativeProj.Situation.relativeProjBaseChange_comp`, asks for the identification of the
graded algebras along `q ≫ g` to be, in every degree, the composite of those along `g` and `q`.
For the symmetric algebra this reduces to degree one: the iterated pullback of a symmetric
algebra is a symmetric algebra on the iterated pullback of the module
(`Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra`), and two unital homomorphisms out
of a symmetric algebra into a commutative graded algebra agree once they agree on the degree-one
generator.  In degree one the identifications of the symmetric algebras are the given
identifications of the modules
(`Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator`), so the compatibility of
`c`, `c'`, `c''` is exactly what is needed.

## Main results

* `Stacks.RelativeProj.pairwiseCommutes_sheafifiedSymmetricAlgebra`: any degree-one map into a
  symmetric algebra has pairwise commuting image.
* `Stacks.RelativeProj.symmetricSituationPullbackHom_comp`: the identifications of the symmetric
  algebras are compatible in every degree, granted the compatibility of the identifications of
  the modules.
* `Stacks.RelativeProj.projectiveBundleBaseChange_comp`: **the composition law** for the
  base-change comparison morphisms of projective bundles.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open SheafOfModules.GradedAlgebra
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.RelativeProj

/-- **Every degree-one map into a symmetric algebra has pairwise commuting image**, because the
symmetric algebra is graded commutative. -/
theorem pairwiseCommutes_sheafifiedSymmetricAlgebra {X : Scheme.{u}} (F : X.Modules)
    {M : X.Modules}
    (κ : M ⟶ (SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
      F).piece 1) :
    PairwiseCommutes κ := fun U _ _ =>
  eq_of_heq (SheafOfModules.mul_comm_sheafifiedSymmetricAlgebra _ F 1 1 U _ _)

variable {X Y Z : Scheme.{u}} (q : X ⟶ Y) (g : Y ⟶ Z) (E : Z.Modules) [E.IsQuasicoherent]
  (E' : Y.Modules) [E'.IsQuasicoherent] (E'' : X.Modules) [E''.IsQuasicoherent]
  (c : E' ≅ (Scheme.Modules.pullback g).obj E) (c' : E'' ≅ (Scheme.Modules.pullback q).obj E')
  (c'' : E'' ≅ (Scheme.Modules.pullback (q ≫ g)).obj E)

/-- **The identifications of the symmetric algebras are compatible in every degree**, as soon as
the identifications of the modules are compatible: `q^*c` followed by `c'` is the canonical
comparison of the iterated pullback followed by `c''`.

Both sides are the degree-`n` components of unital homomorphisms out of the iterated pullback of
the symmetric algebra of `E`, which is a symmetric algebra on the iterated pullback of `E`; the
two homomorphisms agree on the generator by the compatibility hypothesis. -/
theorem symmetricSituationPullbackHom_comp
    (hc : (Scheme.Modules.pullbackComp q g).hom.app E ≫ c''.inv =
      (Scheme.Modules.pullback q).map c.inv ≫ c'.inv) (n : ℤ) :
    canHom q g (q ≫ g) rfl ((symmetricSituationOfQuasicoherent Z E).algebra.piece n) ≫
        (symmetricSituationPullbackHom (q ≫ g) E E'' c'').app n =
      (Scheme.Modules.pullback q).map ((symmetricSituationPullbackHom g E E' c).app n) ≫
        (symmetricSituationPullbackHom q E' E'' c').app n := by
  have hA := Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra q.toLRSHom.toShHom
    (Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra g.toLRSHom.toShHom
      (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥Z) E))
  let L := (baseAlgebraCompHom (symmetricSituationOfQuasicoherent Z E).algebra q g).comp
    (symmetricSituationPullbackHom (q ≫ g) E E'' c'')
  let R := (baseAlgebraMapHom q (symmetricSituationPullbackHom g E E' c)).comp
    (symmetricSituationPullbackHom q E' E'' c')
  have hLR : L = R := by
    refine hA.isUniversal.hom_ext
      (κ := (Scheme.Modules.pullbackComp q g).hom.app E ≫ c''.inv ≫
        SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) E'')
      (pairwiseCommutes_sheafifiedSymmetricAlgebra E'' _) ?_ ?_
    · change (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map
          (SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥Z) E)) ≫
          (Scheme.Modules.pullbackComp q g).hom.app _ ≫
            (symmetricSituationPullbackHom (q ≫ g) E E'' c'').app 1 = _
      exact ((Scheme.Modules.pullbackComp q g).hom.naturality_assoc _ _).trans
        (congrArg ((Scheme.Modules.pullbackComp q g).hom.app E ≫ ·)
          (Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator (q ≫ g) E E'' c''))
    · change (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map
          (SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥Z) E)) ≫
          (Scheme.Modules.pullback q).map ((symmetricSituationPullbackHom g E E' c).app 1) ≫
            (symmetricSituationPullbackHom q E' E'' c').app 1 = _
      exact ((Scheme.Modules.pullback q).map_comp_assoc _ _ _).symm.trans <|
        (congrArg (fun z => (Scheme.Modules.pullback q).map z ≫
          (symmetricSituationPullbackHom q E' E'' c').app 1)
          (Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator g E E' c)).trans <|
        ((Scheme.Modules.pullback q).map_comp_assoc _ _ _).trans <|
        (congrArg ((Scheme.Modules.pullback q).map c.inv ≫ ·)
          (Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator q E' E'' c')).trans
        ((reassoc_of% hc) _).symm
  exact (congrArg (fun z => z ≫ (symmetricSituationPullbackHom (q ≫ g) E E'' c'').app n)
    (canHom_rfl q g ((symmetricSituationOfQuasicoherent Z E).algebra.piece n))).trans
    (congrArg (fun φ : UnitalHom _ _ => φ.app n) hLR)

/-- **The composition law for the base-change comparison of projective bundles.**  For
`q : X ⟶ Y`, `g : Y ⟶ Z` and identifications `c : E' ≅ g^*E`, `c' : E'' ≅ q^*E'`,
`c'' : E'' ≅ (q ≫ g)^*E` compatible through the canonical comparison of the iterated pullback,
the comparison `𝐏(E'') ⟶ 𝐏(E')` followed by `𝐏(E') ⟶ 𝐏(E)` is the comparison
`𝐏(E'') ⟶ 𝐏(E)`. -/
theorem projectiveBundleBaseChange_comp
    (hc : (Scheme.Modules.pullbackComp q g).hom.app E ≫ c''.inv =
      (Scheme.Modules.pullback q).map c.inv ≫ c'.inv) :
    projectiveBundleBaseChange q E' E'' c' ≫ projectiveBundleBaseChange g E E' c =
      projectiveBundleBaseChange (q ≫ g) E E'' c'' :=
  Situation.relativeProjBaseChange_comp
    (s := symmetricSituationOfQuasicoherent Z E) (s' := symmetricSituationOfQuasicoherent Y E')
    (s'' := symmetricSituationOfQuasicoherent X E'') g q
    (symmetricSituationPullbackHom g E E' c)
    (fun m => isIso_symmetricSituationPullbackHom_app g E E' c (m : ℤ))
    (symmetricSituationPullbackHom q E' E'' c')
    (fun m => isIso_symmetricSituationPullbackHom_app q E' E'' c' (m : ℤ))
    (symmetricSituationPullbackHom (q ≫ g) E E'' c'')
    (fun m => isIso_symmetricSituationPullbackHom_app (q ≫ g) E E'' c'' (m : ℤ))
    (fun n => symmetricSituationPullbackHom_comp q g E E' E'' c c' c'' hc (n : ℤ))

end Stacks.RelativeProj

end
