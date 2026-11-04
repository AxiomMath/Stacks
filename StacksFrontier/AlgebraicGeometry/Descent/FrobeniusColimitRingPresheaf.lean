module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictDiagram
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackExtendScalarsModel
public import StacksFrontier.CategoryTheory.Sites.ColimitSheafifyComparison

/-!
# The presheaf colimit underlying the Frobenius colimit of the structure sheaf

`AlgebraicGeometry.frobeniusColimitRingSheaf` is a colimit of sheaves of rings, formed
abstractly, and nothing computes its sections. What *is* computable is the colimit of the
underlying presheaves, which is taken objectwise, and
`CategoryTheory.Sheaf.colimitToColimitObj` says that the sheaf colimit is the sheafification of
it. This file records that comparison for the Frobenius diagram and draws the consequence the
remaining input to Stacks Tag 0EXB needs: **the abelian sheaf underlying the extension of
scalars of a sheaf of `𝒪_X`-modules along a coprojection `𝒪_X ⟶ colim_F 𝒪_X` is the
sheafification of the objectwise tensor products**

`V ↦ (colim_j 𝒪_X(V)) ⊗_{𝒪_X(V)} 𝒢(V)`,

the colimit being the ordinary filtered colimit of rings along the `p`-th power map.

## Main definitions

* `CategoryTheory.Limits.ringPresheafEndoColimit`: the colimit of the underlying presheaves of
  the diagram of iterates of an endomorphism of a sheaf of rings, with
  `CategoryTheory.Limits.ringPresheafEndoColimitι` its coprojections.
* `CategoryTheory.Limits.toRingSheafEndoColimit`: the comparison of that presheaf colimit with
  the underlying presheaf of the colimit of sheaves of rings. It is locally bijective.
* `AlgebraicGeometry.frobeniusRingSheafDiagram`, `AlgebraicGeometry.frobeniusRingPresheaf`,
  `AlgebraicGeometry.frobeniusRingPresheafι` and
  `AlgebraicGeometry.toFrobeniusColimitRingSheaf`: those four objects for the Frobenius
  endomorphism of the structure sheaf, read on the site of opens.

## Main results

* `CategoryTheory.Limits.ringPresheafEndoColimitι_comp_toRingSheafEndoColimit` and
  `CategoryTheory.Limits.comp_ringPresheafEndoColimitι_succ`: the coprojections of the presheaf
  colimit lift those of the sheaf colimit, and absorb one copy of the endomorphism.
* `AlgebraicGeometry.frobeniusStageExtendScalarsCompToSheafIso`: **the abelian sheaf underlying
  `S_n 𝒢`** is the sheafification of the objectwise tensor product.

## Implementation notes

The whole point of routing through a presheaf of rings other than the sections of
`colim_F 𝒪_X` is that `PresheafOfModules.sheafification` accepts any locally bijective
morphism `R₀ ⟶ R` of presheaves of rings, and its composite with
`SheafOfModules.toSheaf` is the abelian sheafification of the underlying abelian presheaf *on
the nose* (`PresheafOfModules.sheafificationCompToSheaf` is `Iso.refl`). So the sections of
`colim_F 𝒪_X`, which are unknown, never appear: only the objectwise filtered colimits of rings
`colim_j 𝒪_X(V)` do.

`AlgebraicGeometry.frobeniusRingSheafDiagram` is the diagram of
`CategoryTheory.Limits.ringSheafEndoColimit` retyped on `Opens X` with its Grothendieck
topology, exactly as `AlgebraicGeometry.Scheme.ringSheafOnOpens` retypes the structure sheaf:
the two spellings are definitionally equal, and the retyped one is the one instance resolution
can use.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- **The colimit of the underlying presheaves of the diagram of iterates of an endomorphism of
a sheaf of rings.** Being a colimit of presheaves it is computed objectwise, as the filtered
colimit of rings `colim_j S(V)` along the iterates of the endomorphism. -/
noncomputable def ringPresheafEndoColimit (ψ : S ⟶ S) : Cᵒᵖ ⥤ RingCat.{u} :=
  colimit (endoSequence ψ ⋙ sheafToPresheaf J RingCat.{u})

/-- The stage-`n` coprojection into the presheaf colimit, with its source read as the
underlying presheaf of `S`. -/
noncomputable def ringPresheafEndoColimitι (ψ : S ⟶ S) (n : ℕ) :
    S.obj ⟶ ringPresheafEndoColimit ψ :=
  colimit.ι (endoSequence ψ ⋙ sheafToPresheaf J RingCat.{u}) n

/-- **The colimit of sheaves of rings along an endomorphism is the sheafification of the
colimit of the underlying presheaves**: this is the comparison morphism, which
`CategoryTheory.Sheaf.w_colimitToColimitObj` shows to be locally bijective. -/
noncomputable def toRingSheafEndoColimit (ψ : S ⟶ S) :
    ringPresheafEndoColimit ψ ⟶ (ringSheafEndoColimit ψ).obj :=
  Sheaf.colimitToColimitObj J (endoSequence ψ)

/-- The comparison from the presheaf colimit to the colimit of sheaves of rings is locally
injective. -/
instance isLocallyInjective_toRingSheafEndoColimit (ψ : S ⟶ S) :
    Presheaf.IsLocallyInjective J (toRingSheafEndoColimit ψ) :=
  Sheaf.isLocallyInjective_colimitToColimitObj J (endoSequence ψ)

/-- The comparison from the presheaf colimit to the colimit of sheaves of rings is locally
surjective. -/
instance isLocallySurjective_toRingSheafEndoColimit (ψ : S ⟶ S) :
    Presheaf.IsLocallySurjective J (toRingSheafEndoColimit ψ) :=
  Sheaf.isLocallySurjective_colimitToColimitObj J (endoSequence ψ)

/-- The coprojections of the presheaf colimit lift those of the colimit of sheaves of rings. -/
lemma ringPresheafEndoColimitι_comp_toRingSheafEndoColimit (ψ : S ⟶ S) (n : ℕ) :
    ringPresheafEndoColimitι ψ n ≫ toRingSheafEndoColimit ψ =
      (ringSheafEndoColimitι ψ n).hom :=
  Sheaf.ι_colimitToColimitObj J (endoSequence ψ) n

/-- Passing from stage `n` to stage `n + 1` of the presheaf colimit absorbs one copy of the
endomorphism. -/
lemma comp_ringPresheafEndoColimitι_succ (ψ : S ⟶ S) (n : ℕ) :
    ψ.hom ≫ ringPresheafEndoColimitι ψ (n + 1) = ringPresheafEndoColimitι ψ n := by
  have h := colimit.w (endoSequence ψ ⋙ sheafToPresheaf J RingCat.{u})
    (homOfLE (Nat.le_add_right n 1))
  rwa [Functor.comp_map, endoSequence_map_succ] at h

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- Frobenius on the structure sheaf, read as an endomorphism of
`AlgebraicGeometry.Scheme.ringSheafOnOpens`. This is
`AlgebraicGeometry.frobeniusRingCatSheafHom`; only its type is spelled differently, so that
instance resolution can see the site and its topology. -/
noncomputable def frobeniusRingSheafHom : X.ringSheafOnOpens ⟶ X.ringSheafOnOpens :=
  frobeniusRingCatSheafHom X p hX

/-- The diagram `𝒪_X → 𝒪_X → ⋯` of iterates of Frobenius, read on the site of opens. -/
noncomputable def frobeniusRingSheafDiagram :
    ℕ ⥤ Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} :=
  endoSequence (frobeniusRingSheafHom X p hX)

/-- **The presheaf of rings `V ↦ colim_j 𝒪_X(V)`**, the objectwise filtered colimit of the
sections of the structure sheaf along the `p`-th power map, whose sheafification is
`colim_F 𝒪_X`. -/
noncomputable def frobeniusRingPresheaf : (Opens (X : TopCat))ᵒᵖ ⥤ RingCat.{u} :=
  ringPresheafEndoColimit (frobeniusRingSheafHom X p hX)

/-- The stage-`n` coprojection `𝒪_X ⟶ colim_j 𝒪_X` of presheaves of rings. -/
noncomputable def frobeniusRingPresheafι (n : ℕ) :
    X.ringSheafOnOpens.obj ⟶ frobeniusRingPresheaf X p hX :=
  ringPresheafEndoColimitι (frobeniusRingSheafHom X p hX) n

/-- **`colim_F 𝒪_X` is the sheafification of the presheaf `V ↦ colim_j 𝒪_X(V)`**: this is the
comparison morphism, and it is locally bijective. -/
noncomputable def toFrobeniusColimitRingSheaf :
    frobeniusRingPresheaf X p hX ⟶ (frobeniusColimitRingSheaf X p hX).obj :=
  toRingSheafEndoColimit (frobeniusRingSheafHom X p hX)

/-- The comparison `(V ↦ colim_j 𝒪_X(V)) ⟶ colim_F 𝒪_X` is locally injective. -/
instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology (X : TopCat))
    (toFrobeniusColimitRingSheaf X p hX) :=
  isLocallyInjective_toRingSheafEndoColimit (frobeniusRingSheafHom X p hX)

/-- The comparison `(V ↦ colim_j 𝒪_X(V)) ⟶ colim_F 𝒪_X` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
    (toFrobeniusColimitRingSheaf X p hX) :=
  isLocallySurjective_toRingSheafEndoColimit (frobeniusRingSheafHom X p hX)

/-- The stage-`n` presheaf coprojection lifts the stage-`n` coprojection of sheaves of
rings. -/
lemma frobeniusRingPresheafι_comp_toFrobeniusColimitRingSheaf (n : ℕ) :
    frobeniusRingPresheafι X p hX n ≫ toFrobeniusColimitRingSheaf X p hX =
      (frobeniusStageStructureMap X p hX n).hom :=
  ringPresheafEndoColimitι_comp_toRingSheafEndoColimit (frobeniusRingSheafHom X p hX) n

/-- Passing from stage `n` to stage `n + 1` of the presheaf colimit absorbs one Frobenius. -/
lemma frobenius_comp_frobeniusRingPresheafι_succ (n : ℕ) :
    (frobeniusSelfStructureMap X p hX).hom ≫ frobeniusRingPresheafι X p hX (n + 1) =
      frobeniusRingPresheafι X p hX n :=
  comp_ringPresheafEndoColimitι_succ (frobeniusRingSheafHom X p hX) n

/-- The hypothesis of `Stacks.SheafOfModules.pullbackIsoExtendScalars` for the stage-`n`
coprojection: restriction of scalars along the presheaf coprojection after restriction of
scalars along the sheafification comparison is restriction of scalars along the coprojection of
sheaves of rings, which is the pushforward of sheaves of modules read on presheaves. -/
lemma restrictScalars_frobeniusRingPresheafι_comp (n : ℕ) :
    (_root_.SheafOfModules.forget (frobeniusColimitRingSheaf X p hX) ⋙
          PresheafOfModules.restrictScalars (toFrobeniusColimitRingSheaf X p hX)) ⋙
        PresheafOfModules.restrictScalars.{u} (frobeniusRingPresheafι X p hX n) =
      (_root_.SheafOfModules.forget (frobeniusColimitRingSheaf X p hX) ⋙
          PresheafOfModules.restrictScalars (𝟙 (frobeniusColimitRingSheaf X p hX).obj)) ⋙
        PresheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n).hom :=
  congrArg
    (fun f => _root_.SheafOfModules.forget (frobeniusColimitRingSheaf X p hX) ⋙
      PresheafOfModules.restrictScalars.{u} f)
    (frobeniusRingPresheafι_comp_toFrobeniusColimitRingSheaf X p hX n)

/-- **The abelian sheaf underlying `S_n 𝒢`, the extension of scalars of a sheaf of
`𝒪_X`-modules along the stage-`n` coprojection, is the sheafification of the objectwise tensor
product** `V ↦ (colim_j 𝒪_X(V)) ⊗_{𝒪_X(V)} 𝒢(V)`. The sections of `colim_F 𝒪_X` do not
appear. -/
noncomputable def frobeniusStageExtendScalarsCompToSheafIso (n : ℕ) :
    frobeniusStageExtendScalars X p hX n ⋙
        _root_.SheafOfModules.toSheaf (frobeniusColimitRingSheaf X p hX) ≅
      _root_.SheafOfModules.forget X.ringSheafOnOpens ⋙
        Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u}
            (frobeniusRingPresheafι X p hX n) ⋙
          PresheafOfModules.toPresheaf (frobeniusRingPresheaf X p hX) ⋙
            presheafToSheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.pullbackCompToSheafIso (frobeniusStageStructureMap X p hX n)
    (toFrobeniusColimitRingSheaf X p hX) (frobeniusRingPresheafι X p hX n)
    (restrictScalars_frobeniusRingPresheafι_comp X p hX n)

end AlgebraicGeometry

end
