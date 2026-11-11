module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint

/-!
# Base change of abelian schemes

An abelian scheme over `W` is a commutative flat proper group scheme of finite presentation over
`W` all of whose fibres are abelian varieties. This file shows that the class of abelian schemes
is stable under base change along an arbitrary morphism of schemes `f : X ⟶ W`.

## Main results

* `AlgebraicGeometry.grpObjOverPullbackObj`: the base change `G_X` of a group scheme `G` over
  `W` along `f : X ⟶ W` is a group scheme over `X`.
* `AlgebraicGeometry.IsAbelianVariety.of_iso`: being an abelian variety only depends on the
  isomorphism class of the underlying scheme over the field.
* `AlgebraicGeometry.isAbelianScheme_overPullbackObj`: the base change of an abelian scheme
  along `f : X ⟶ W` is an abelian scheme over `X`; `AlgebraicGeometry.isAbelianScheme_mapGrpObj`
  is the same statement with the group object `(Over.pullback f).mapGrp.obj (.mk G)` written out.

## Implementation notes

The fibre of `G_X` at a point `x` of `X` is the pullback of `G` along the composite
`Spec κ(x) ⟶ X ⟶ W`, which also factors as `Spec κ(x) ⟶ Spec κ(f x) ⟶ W`. Hence it is
isomorphic, over `Spec κ(x)`, to the base change of the fibre of `G` at `f x` along the field
extension `κ(x) / κ(f x)`, which is an abelian variety by Stacks 0BFB
(`AlgebraicGeometry.isAbelianVariety_pullbackObj`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Being an abelian variety over a field `k` is invariant under isomorphism of schemes over
`Spec k`; the group-object structures on the two sides play no role. -/
theorem IsAbelianVariety.of_iso {k : Type u} [Field k] {A B : Over (Spec (.of k))} [GrpObj A]
    [GrpObj B] (e : A ≅ B) [IsAbelianVariety k A] : IsAbelianVariety k B := by
  let e' : A.left ≅ B.left := (Over.forget _).mapIso e
  have hB : B.hom = e'.inv ≫ A.hom := (Over.w e.inv).symm
  have : Nonempty B.left := ⟨e'.hom (Nonempty.some inferInstance)⟩
  have : IsIntegral B.left := isIntegral_of_isOpenImmersion e'.inv
  have : GeometricallyIntegral B.hom := by
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    have hsq : IsPullback e'.inv B.hom A.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hB, Category.comp_id]⟩
    exact GeometricallyIntegral.geometrically_isIntegral (f := A.hom) y (fst ≫ e'.inv) snd
      (by simpa using h.paste_horiz hsq)
  have : IsSeparated B.hom := by rw [hB]; infer_instance
  have : LocallyOfFiniteType B.hom := by rw [hB]; infer_instance
  have : QuasiCompact B.hom := by rw [hB]; infer_instance
  have : IsProper B.hom := by rw [hB]; infer_instance
  exact .mk (toIsProperVariety := .mk (toIsVariety := .mk))

variable {X W : Scheme.{u}} (f : X ⟶ W) (G : Over W) [GrpObj G]

/-- The base change of a group scheme over `W` along `f : X ⟶ W` is a group scheme over `X`. -/
noncomputable instance grpObjOverPullbackObj : GrpObj ((Over.pullback f).obj G) :=
  ((Over.pullback f).mapGrp.obj (.mk G)).grp

/-- The base change of a commutative group scheme over `W` along `f : X ⟶ W` is commutative. -/
instance isCommMonObj_overPullbackObj [IsCommMonObj G] :
    IsCommMonObj ((Over.pullback f).obj G) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback f).mapCommMon.obj (.mk G)).X)

/-- The fibre at `x` of the base change of `G` along `f` is isomorphic, over `Spec κ(x)`, to the
base change of the fibre of `G` at `f x` along the residue field extension `κ(x) / κ(f x)`. -/
def overPullbackFibreIso (x : X) :
    (Over.pullback (Spec.map (f.residueFieldMap x))).obj
        ((Over.pullback (W.fromSpecResidueField (f x))).obj G) ≅
      (Over.pullback (X.fromSpecResidueField x)).obj ((Over.pullback f).obj G) :=
  ((Over.pullbackComp _ _).app G).symm ≪≫
    eqToIso (congrArg (fun g => (Over.pullback g).obj G)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x)) ≪≫
    (Over.pullbackComp _ _).app G

/-- **Abelian schemes are stable under base change.** The base change of an abelian scheme over
`W` along any morphism `f : X ⟶ W` is an abelian scheme over `X`. -/
instance isAbelianScheme_overPullbackObj [IsAbelianScheme G] :
    IsAbelianScheme ((Over.pullback f).obj G) where
  toFlat := inferInstanceAs (Flat (pullback.snd G.hom f))
  toIsProper := inferInstanceAs (IsProper (pullback.snd G.hom f))
  toLocallyOfFinitePresentation :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.hom f))
  fibre_isAbelianVariety x := by
    let _ : Algebra (W.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have := IsAbelianScheme.fibre_isAbelianVariety (G := G) (f x)
    have hA : IsAbelianVariety (X.residueField x)
        ((Over.pullback (Spec.map (f.residueFieldMap x))).obj
          ((Over.pullback (W.fromSpecResidueField (f x))).obj G)) :=
      isAbelianVariety_pullbackObj (k := W.residueField (f x)) (K := X.residueField x)
        ((Over.pullback (W.fromSpecResidueField (f x))).mapGrp.obj (.mk G)).X
    exact IsAbelianVariety.of_iso (overPullbackFibreIso f G x)

/-- The base change of an abelian scheme along `f : X ⟶ W`, in the form of the group object
`(Over.pullback f).mapGrp.obj (.mk G)`, is an abelian scheme over `X`. This is
`AlgebraicGeometry.isAbelianScheme_overPullbackObj` with the group structure written out, for
use where instance search does not see through the projections of `Grp`. -/
theorem isAbelianScheme_mapGrpObj [IsAbelianScheme G] :
    @IsAbelianScheme X ((Over.pullback f).mapGrp.obj (.mk G)).X
      ((Over.pullback f).mapGrp.obj (.mk G)).grp :=
  isAbelianScheme_overPullbackObj f G

end AlgebraicGeometry
