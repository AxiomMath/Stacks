module

public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A module over a quasi-coherent algebra which is quasi-coherent downstairs

Let `S` be a scheme and let `α : 𝒪_S ⟶ A` be a sheaf of rings on `S` which is quasi-coherent as
an `𝒪_S`-module, i.e. a quasi-coherent `𝒪_S`-algebra.  This file proves the implication of
Stacks Tag 0H88 left open by
`Stacks.AlgebraicGeometry.QcohOverAlgebra.isQuasicoherent_restrictScalars`: an `A`-module which
is quasi-coherent as an `𝒪_S`-module is quasi-coherent as an `A`-module.  Together with that
file this gives Tag 0H88 as an iff, and hence the second assertion of Stacks Tag 01SB, together
with the quasi-coherence over `f_* 𝒪_X` of a direct image along an affine morphism, which is
the first half of the first assertion of Tag 01SB.

## Main results

* `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars`: the
  implication of Stacks Tag 0H88 proved here, for an arbitrary quasi-coherent `𝒪_S`-algebra.
* `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_restrictScalars_iff`: Stacks Tag 0H88 as
  an iff, for an arbitrary quasi-coherent `𝒪_S`-algebra.
* `Stacks.AlgebraicGeometry.QcohLimits.affinePushforward_isQuasicoherent`: for an affine
  morphism `f : X ⟶ S`, the direct image of a quasi-coherent `𝒪_X`-module is quasi-coherent as
  a module over `f_* 𝒪_X`.
* `Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff`: the second
  assertion of Stacks Tag 01SB, i.e. Tag 0H88 for `A = f_* 𝒪_X`.

## Implementation notes

The construction follows the second half of the proof of Tag 0H88, but it replaces the
`Spec`-level bookkeeping of that argument by the transfers already available.  On an affine open
`W` of `S` a presentation of `G.over W` as an `A.over W`-module needs generators and relations.
Both are produced over `𝒪_S.over W` and transferred by
`Stacks.AlgebraicGeometry.QcohOverAlgebra.generatingSectionsOfRestrictScalars`, which says that
a family of sections generating a module after restriction of scalars already generates it.

Over `𝒪_S.over W` the two families come from global presentations on the affine scheme
`W.toScheme`, through `overScheme` below: restriction of scalars along `overHom α W` followed by
`AlgebraicGeometry.Scheme.Modules.overEquiv`.  For the generators the module in question is
`G` restricted, quasi-coherent by hypothesis.  For the relations it is the kernel of the
morphism from a free module attached to the generators; `overScheme` preserves finite limits, so
that kernel is carried to the kernel of a morphism between two quasi-coherent `𝒪`-modules on
`W.toScheme` — the source is a coproduct of copies of the image of the unit, quasi-coherent
because `overScheme` preserves colimits and the algebra is quasi-coherent — and is therefore
quasi-coherent by
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`.  This is the only place where
closure of quasi-coherence under kernels is used, and it is the reason the implication was out
of reach before.

## References

* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.QcohLimits

variable {S : Scheme.{u}}
  {A : Sheaf (Opens.grothendieckTopology S.toPresheafedSpace.carrier) RingCat.{u}}
  (α : S.ringCatSheaf ⟶ A)

/-! ### From `A`-modules on the slice over an open to modules on the open subscheme -/

/-- For an open `W` of `S`, this is the functor from `A.over W`-modules on the slice site over
`W` to `𝒪_W`-modules on the open subscheme `W`: restrict scalars to `𝒪_S.over W` and transport
along `AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
def overScheme (W : S.Opens) : SheafOfModules.{u} (A.over W) ⥤ W.toScheme.Modules :=
  SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W) ⋙
    (Scheme.Modules.overEquiv W).functor

/-- `overScheme` preserves colimits: both of its factors do. -/
instance preservesColimitsOfSize_overScheme (W : S.Opens) :
    PreservesColimitsOfSize.{u, u} (overScheme α W) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W) ⋙
      (Scheme.Modules.overEquiv W).functor))

/-- `overScheme` preserves finite limits: restriction of scalars does, and the second factor is
an equivalence. -/
instance preservesFiniteLimits_overScheme (W : S.Opens) :
    PreservesFiniteLimits (overScheme α W) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W) ⋙
      (Scheme.Modules.overEquiv W).functor))

/-- `overScheme` preserves zero morphisms. -/
instance preservesZeroMorphisms_overScheme (W : S.Opens) :
    (overScheme α W).PreservesZeroMorphisms :=
  inferInstanceAs ((SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W) ⋙
    (Scheme.Modules.overEquiv W).functor).PreservesZeroMorphisms)

/-- For an `A`-module `G` and an open `W` of `S`, `overScheme` carries the restriction of `G` to
the slice over `W` to the restriction to `W` of the restriction of scalars of `G`. -/
def overSchemeObjIso (G : SheafOfModules.{u} A) (W : S.Opens) :
    (overScheme α W).obj (SheafOfModules.over G W) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj
        ((SheafOfModules.restrictScalars.{u} α).obj G) :=
  (Scheme.Modules.overFunctorEquiv W).app ((SheafOfModules.restrictScalars.{u} α).obj G)

/-- `overScheme` carries the unit `A.over W`-module to the restriction to `W` of the restriction
of scalars of the unit `A`-module. -/
def overSchemeUnitIso (W : S.Opens) :
    (overScheme α W).obj (SheafOfModules.unit (A.over W)) ≅
      (Scheme.Modules.restrictFunctor W.ι).obj
        ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)) :=
  (Scheme.Modules.overEquiv W).functor.mapIso
      (eqToIso (QcohOverAlgebra.restrictScalars_over_unit α W)) ≪≫
    (Scheme.Modules.overFunctorEquiv W).app
      ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A))

/-- Transport of a presentation along `AlgebraicGeometry.Scheme.Modules.overEquiv`: a
presentation of the `𝒪_W`-module attached to an `𝒪_S.over W`-module gives a presentation of
that `𝒪_S.over W`-module.  This is the version of
`Stacks.AlgebraicGeometry.AffinePushforward.presentationOver` for a module on the slice site
which is not visibly the restriction of a module on `S`. -/
def presentationOfOverEquiv {W : S.Opens} (P : SheafOfModules.{u} (S.ringCatSheaf.over W))
    (Q : ((Scheme.Modules.overEquiv W).functor.obj P).Presentation) : P.Presentation :=
  AffinePushforward.presentationOfIso ((Scheme.Modules.overEquiv W).unitIso.app P).symm
    (@SheafOfModules.Presentation.map.{u, u, u, u, u} _ _ _ _ _ _ _ _ _ _ _ _ _ Q
      (Scheme.Modules.overEquiv W).inverse
      (inferInstance : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv W).inverse)
      (AffinePushforward.overInverseUnitIso W))

/-! ### The local statement -/

/-- If the restriction of scalars of the unit `A`-module is quasi-coherent and an `A`-module `G`
is quasi-coherent after restriction of scalars, then `G` has a presentation over the slice site
over every affine open of `S`. -/
def presentationOverAffine
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    (G : SheafOfModules.{u} A)
    (hG : ((SheafOfModules.restrictScalars.{u} α).obj G).IsQuasicoherent)
    {W : S.Opens} (hW : IsAffineOpen W) : (SheafOfModules.over G W).Presentation := by
  have _hA := hA
  have _hG := hG
  have hunit : ((overScheme α W).obj (SheafOfModules.unit (A.over W))).IsQuasicoherent := by
    refine (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (overSchemeUnitIso α W).symm ?_
    exact Scheme.Modules.isQuasicoherent_restrictFunctor W.ι _
  have _hsmall : PreservesColimitsOfSize.{0, 0} (overScheme α W) :=
    preservesSmallestColimits_of_preservesColimits.{u, u} _
  have hfree : ∀ I : Type u,
      ((overScheme α W).obj (SheafOfModules.free.{u} (R := A.over W) I)).IsQuasicoherent :=
    fun I ↦ QuasicoherentColimits.isQuasicoherent_of_isColimit (fun _ ↦ hunit)
      (isColimitOfPreserves (overScheme α W) (SheafOfModules.isColimitFreeCofan I))
  have hGW : ((overScheme α W).obj (SheafOfModules.over G W)).IsQuasicoherent := by
    refine (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (overSchemeObjIso α G W).symm ?_
    exact Scheme.Modules.isQuasicoherent_restrictFunctor W.ι _
  set gen := QcohOverAlgebra.generatingSectionsOfRestrictScalars (QcohOverAlgebra.overHom α W)
    (presentationOfOverEquiv
      ((SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W)).obj
        (SheafOfModules.over G W))
      (AffinePushforward.nonempty_presentation_of_isoSpec hW.isoSpec
        ((overScheme α W).obj (SheafOfModules.over G W))).some).generators with hgen
  have hker : ((overScheme α W).obj (kernel gen.π)).IsQuasicoherent := by
    have h1 := hfree gen.I
    have h2 := hGW
    have hk : (kernel ((overScheme α W).map gen.π)).IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (asIso (kernelComparison gen.π (overScheme α W))).symm hk
  exact { generators := gen
          relations := QcohOverAlgebra.generatingSectionsOfRestrictScalars
            (QcohOverAlgebra.overHom α W)
            (presentationOfOverEquiv
              ((SheafOfModules.restrictScalars.{u} (QcohOverAlgebra.overHom α W)).obj
                (kernel gen.π))
              (AffinePushforward.nonempty_presentation_of_isoSpec hW.isoSpec
                ((overScheme α W).obj (kernel gen.π))).some).generators }

/-! ### Stacks Tag 0H88 -/

/-- **Stacks Project, Tag 0H88, the other implication.** Let `α : 𝒪_S ⟶ A` be a sheaf of rings
on a scheme `S` which is quasi-coherent as an `𝒪_S`-module.  An `A`-module which is
quasi-coherent as an `𝒪_S`-module is quasi-coherent as an `A`-module. -/
theorem isQuasicoherent_of_isQuasicoherent_restrictScalars
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    (G : SheafOfModules.{u} A)
    (hG : ((SheafOfModules.restrictScalars.{u} α).obj G).IsQuasicoherent) :
    G.IsQuasicoherent := by
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := G) ?_
  exact
    { I := S.affineOpens
      X := fun V ↦ (V : S.Opens)
      coversTop := (Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (iSup_affineOpens_eq_top S))
      presentation := fun V ↦ presentationOverAffine α hA G hG V.2 }

/-- **Stacks Project, Tag 0H88.** Let `α : 𝒪_S ⟶ A` be a sheaf of rings on a scheme `S` which is
quasi-coherent as an `𝒪_S`-module.  An `A`-module is quasi-coherent as an `𝒪_S`-module if and
only if it is quasi-coherent as an `A`-module. -/
@[stacks 0H88, ega "I 9.6.1"]
theorem isQuasicoherent_restrictScalars_iff
    (hA : ((SheafOfModules.restrictScalars.{u} α).obj (SheafOfModules.unit A)).IsQuasicoherent)
    (G : SheafOfModules.{u} A) :
    ((SheafOfModules.restrictScalars.{u} α).obj G).IsQuasicoherent ↔ G.IsQuasicoherent :=
  ⟨fun h ↦ isQuasicoherent_of_isQuasicoherent_restrictScalars α hA G h,
    fun h ↦ have := h; QcohOverAlgebra.isQuasicoherent_restrictScalars α hA G⟩

/-! ### Stacks Tag 01SB -/

variable {X S : Scheme.{u}}

/-- For an affine morphism `f : X ⟶ S`, an `f_* 𝒪_X`-module which is quasi-coherent as an
`𝒪_S`-module is quasi-coherent as an `f_* 𝒪_X`-module. -/
theorem isQuasicoherent_of_restrictScalars_pushforwardRing (f : X ⟶ S) [IsAffineHom f]
    (G : SheafOfModules.{u} (AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf))
    (hG : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent) :
    G.IsQuasicoherent :=
  isQuasicoherent_of_isQuasicoherent_restrictScalars
    (A := AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf) f.toRingCatSheafHom
    (AffineQcohPushforward.isQuasicoherent_restrictScalars_pushforwardRing f) G hG

/-- Pushforward along an affine morphism, regarded as a module over the pushed-forward
structure sheaf, preserves quasi-coherence.  This is the closure fact used to define the
restricted pushforward functor of Stacks Tag 01SB. -/
theorem affinePushforward_isQuasicoherent (f : X ⟶ S) [IsAffineHom f] (M : X.Modules)
    (hM : M.IsQuasicoherent) :
    ((AffineQcohPushforward.pushforwardModules.{u} f.base X.ringCatSheaf).obj
      M).IsQuasicoherent :=
  have := hM
  AffineQcohPushforward.isQuasicoherent_pushforwardModules_of_reflects f
    (fun G hG ↦ isQuasicoherent_of_restrictScalars_pushforwardRing f G hG) M

/-- **Stacks Project, Tag 01SB, second assertion.** An `f_* 𝒪_X`-module is quasi-coherent as an
`𝒪_S`-module if and only if it is quasi-coherent as an `f_* 𝒪_X`-module.

This is the whole of the tag's final statement ("Moreover, an `𝒜`-module is quasi-coherent as an
`𝒪_S`-module if and only if it is quasi-coherent as an `𝒜`-module").  The tag's other assertion,
the equivalence of categories, is not proved here, so the attribute is clause-qualified. -/
@[stacks 01SB "quasi-coherence under scalar restriction", ega "II 1.4.3" "special case"]
theorem affine_isQuasicoherent_restrictScalars_iff (f : X ⟶ S) [IsAffineHom f]
    (G : SheafOfModules.{u} (AffineQcohPushforward.pushforwardRing f.base X.ringCatSheaf)) :
    ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent ↔
      G.IsQuasicoherent :=
  ⟨fun h ↦ isQuasicoherent_of_restrictScalars_pushforwardRing f G h,
    fun h ↦ have := h
      QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules f G⟩

end Stacks.AlgebraicGeometry.QcohLimits

end

end
