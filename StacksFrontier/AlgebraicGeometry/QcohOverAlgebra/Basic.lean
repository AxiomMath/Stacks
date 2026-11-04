module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars

/-!
# A quasi-coherent module over a quasi-coherent algebra is quasi-coherent

Let `S` be a scheme and let `α : 𝒪_S ⟶ A` be a sheaf of rings on `S` which is quasi-coherent
as an `𝒪_S`-module, i.e. a quasi-coherent `𝒪_S`-algebra.  This file proves one of the two
implications of Stacks Tag 0H88: an `A`-module which is quasi-coherent as an `A`-module is
quasi-coherent as an `𝒪_S`-module.

## Main results

* `Stacks.AlgebraicGeometry.QcohOverAlgebra.isQuasicoherent_restrictScalars`: the implication
  of Stacks Tag 0H88 proved here, for an arbitrary quasi-coherent `𝒪_S`-algebra.
* `Stacks.AlgebraicGeometry.QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules`:
  the case of `A = f_* 𝒪_X` for an affine morphism `f : X ⟶ S`, which is the direction of
  Stacks Tag 0H88 used by Stacks Tag 01SB.

## Implementation notes

No affine cover of `A` and no use of the functor `~` is needed.  Quasi-coherence of an
`A`-module `G` provides a covering `W i` of `S` and, on the slice site over each `W i`, a
presentation of `G` by coproducts of copies of `A`.  Restriction of scalars preserves colimits
(`Stacks.AlgebraicGeometry.RestrictScalarsColimits`), so after restricting scalars this exhibits
`G` over `W i` as a cokernel of a morphism of coproducts of copies of `A`, all of which are
quasi-coherent `𝒪_S`-modules by hypothesis; quasi-coherent modules on a scheme are closed under
colimits (`Stacks.AlgebraicGeometry.QuasicoherentColimits`), so the cokernel is quasi-coherent.

The transfer between the slice site over `W : S.Opens` and the open subscheme `W.toScheme` is
`AlgebraicGeometry.Scheme.Modules.overEquiv`, and the composite functor that performs it is
`overRestrict` below.  It is applied to opens `V ≤ W` with `V` affine, so that the resulting
quasi-coherent modules can be turned into presentations by
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec` and glued by
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`; the affine opens
refining a given covering still cover `S` because they form a basis.

The two commutations `restrictScalars_comp_overFunctor` and `restrictScalars_over_unit` hold by
`rfl`: restriction to a slice and restriction of scalars act on different parts of the data of a
sheaf of modules.

## References

* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.QcohOverAlgebra

variable {S : Scheme.{u}}
  {A : Sheaf (Opens.grothendieckTopology S.toPresheafedSpace.carrier) RingCat.{u}}
  (α : S.ringCatSheaf ⟶ A)

/-! ### Restriction of scalars and restriction to a slice -/

/-- A morphism of sheaves of rings on `S`, restricted to the slice site over an open `W`. -/
noncomputable def overHom (W : S.Opens) : S.ringCatSheaf.over W ⟶ A.over W :=
  (GrothendieckTopology.overPullback _ RingCat.{u} W).map α

/-- Restricting scalars and then restricting to the slice over `W` is restricting to the slice
over `W` and then restricting scalars. -/
theorem restrictScalars_comp_overFunctor (W : S.Opens) :
    SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.overFunctor S.ringCatSheaf W =
      SheafOfModules.overFunctor A W ⋙ SheafOfModules.restrictScalars.{u} (overHom α W) :=
  rfl

/-- The restriction of scalars of the unit `A.over W`-module is the restriction to the slice
over `W` of the restriction of scalars of the unit `A`-module. -/
theorem restrictScalars_over_unit (W : S.Opens) :
    (SheafOfModules.restrictScalars.{u} (overHom α W)).obj (SheafOfModules.unit (A.over W)) =
      SheafOfModules.over
        ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)) W :=
  rfl

/-! ### From the slice over an open to an open subscheme of it -/

/-- For opens `V ≤ W` of `S`, this is the functor from `A.over W`-modules on the slice site over
`W` to `𝒪_V`-modules on the open subscheme `V`: restrict scalars to `𝒪_S.over W`, transport
along `AlgebraicGeometry.Scheme.Modules.overEquiv` to `𝒪_W`-modules on `W`, and restrict to
`V`. -/
noncomputable def overRestrict {V W : S.Opens} (h : V ≤ W) :
    SheafOfModules.{u} (A.over W) ⥤ V.toScheme.Modules :=
  SheafOfModules.restrictScalars.{u} (overHom α W) ⋙ (Scheme.Modules.overEquiv W).functor ⋙
    Scheme.Modules.restrictFunctor (S.homOfLE h)

/-- `overRestrict` preserves colimits: each of its three factors does. -/
instance preservesColimitsOfSize_overRestrict {V W : S.Opens} (h : V ≤ W) :
    PreservesColimitsOfSize.{u, u} (overRestrict α h) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (SheafOfModules.restrictScalars.{u} (overHom α W) ⋙ (Scheme.Modules.overEquiv W).functor ⋙
      Scheme.Modules.restrictFunctor (S.homOfLE h)))

/-- For an `𝒪_S`-module `N` and opens `V ≤ W` of `S`, transporting the restriction of `N` to the
slice over `W` to the open subscheme `W` and then restricting to `V` gives the restriction of
`N` to `V`. -/
noncomputable def overRestrictIso (N : S.Modules) {V W : S.Opens} (h : V ≤ W) :
    (Scheme.Modules.restrictFunctor (S.homOfLE h)).obj
        ((Scheme.Modules.overEquiv W).functor.obj
          ((SheafOfModules.overFunctor S.ringCatSheaf W).obj N)) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj N :=
  (Scheme.Modules.restrictFunctor (S.homOfLE h)).mapIso
      ((Scheme.Modules.overFunctorEquiv W).app N) ≪≫
    ((Scheme.Modules.restrictFunctorComp (S.homOfLE h) W.ι).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (S.homOfLE_ι h)).app N

/-! ### The local statement -/

/-- If the restriction of scalars of the unit `A`-module is quasi-coherent, then for opens
`V ≤ W` of `S` and an `A`-module `G` with a presentation over the slice over `W`, the
restriction to `V` of the restriction of scalars of `G` is quasi-coherent. -/
theorem isQuasicoherent_restrict_of_presentation
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    {V W : S.Opens} (h : V ≤ W) (G : SheafOfModules.{u} A)
    (P : (SheafOfModules.over G W).Presentation) :
    ((Scheme.Modules.restrictFunctor V.ι).obj
      ((SheafOfModules.restrictScalars.{u} α).obj G)).IsQuasicoherent := by
  have _hA := hA
  have _hsmall : PreservesColimitsOfSize.{0, 0} (overRestrict α h) :=
    preservesSmallestColimits_of_preservesColimits.{u, u} _
  have hunit : ((overRestrict α h).obj (SheafOfModules.unit (A.over W))).IsQuasicoherent := by
    have h1 : ((Scheme.Modules.restrictFunctor V.ι).obj
        ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A))).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor V.ι _
    refine (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso ?_ h1
    exact (overRestrictIso ((SheafOfModules.restrictScalars.{u} α).obj
      (SheafOfModules.unit A)) h).symm
  have hfree : ∀ I : Type u,
      ((overRestrict α h).obj (SheafOfModules.free.{u} (R := A.over W) I)).IsQuasicoherent :=
    fun I ↦ QuasicoherentColimits.isQuasicoherent_of_isColimit (fun _ ↦ hunit)
      (isColimitOfPreserves (overRestrict α h) (SheafOfModules.isColimitFreeCofan I))
  have key : ((overRestrict α h).obj (SheafOfModules.over G W)).IsQuasicoherent := by
    refine QuasicoherentColimits.isQuasicoherent_of_isColimit ?_
      (isColimitOfPreserves (overRestrict α h) P.isColimit)
    rintro (_ | _)
    · exact hfree _
    · exact hfree _
  refine (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso ?_ key
  exact overRestrictIso ((SheafOfModules.restrictScalars.{u} α).obj G) h

/-! ### The theorem -/

/-- **Stacks Project, Tag 0H88, one implication.** Let `α : 𝒪_S ⟶ A` be a sheaf of rings on a
scheme `S` which is quasi-coherent as an `𝒪_S`-module.  An `A`-module which is quasi-coherent
as an `A`-module is quasi-coherent as an `𝒪_S`-module. -/
theorem isQuasicoherent_restrictScalars
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    (G : SheafOfModules.{u} A) [G.IsQuasicoherent] :
    ((SheafOfModules.restrictScalars.{u} α).obj G).IsQuasicoherent := by
  obtain ⟨q⟩ := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  refine AffinePushforward.isQuasicoherent_of_presentations _ _
    (S.isBasis_affineOpens.isOpenCover_mem_and_le hcov) fun W ↦ ?_
  obtain ⟨⟨V, i⟩, hVaff, hle⟩ := W
  have hV : IsAffineOpen (V : S.Opens) := hVaff
  have _hqc := isQuasicoherent_restrict_of_presentation α hA hle G (q.presentation i)
  exact (AffinePushforward.nonempty_presentation_of_isoSpec hV.isoSpec _).some

/-- **Stacks Project, Tag 0H88, one implication, for the direct image of the structure sheaf.**
For an affine morphism `f : X ⟶ S`, an `f_* 𝒪_X`-module which is quasi-coherent as an
`f_* 𝒪_X`-module is quasi-coherent as an `𝒪_S`-module. -/
theorem isQuasicoherent_restrictScalars_pushforwardModules {X : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f]
    (G : SheafOfModules.{u} (AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf))
    [G.IsQuasicoherent] :
    ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent :=
  isQuasicoherent_restrictScalars
    (A := AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf) f.toRingCatSheafHom
    (AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing f) G

end Stacks.AlgebraicGeometry.QcohOverAlgebra

end
