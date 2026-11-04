module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.SmoothProjectiveScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Base change of smooth projective schemes along a field extension

The functor `X ↦ X_{k'} = X ×_{Spec k} Spec k'` from smooth projective
schemes over `k` to smooth projective schemes over `k'`, with its projection `X_{k'} ⟶ X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- **Base change `X ↦ X_{k'}`** of smooth projective schemes along a field extension `k'/k`. -/
def baseChange : (SmoothProjectiveScheme k).FullSubcategory ⥤
    (SmoothProjectiveScheme k').FullSubcategory :=
  ObjectProperty.lift _ ((SmoothProjectiveScheme k).ι ⋙ Over.pullback (ArtinSchreier.specExt k k'))
    fun X => ⟨have := X.2.1;
      inferInstanceAs (Smooth (pullback.snd X.obj.hom (ArtinSchreier.specExt k k'))),
      (isStableUnderBaseChange_isProjective).of_isPullback (IsPullback.of_hasPullback _ _) X.2.2⟩

variable {k k'}

/-- The projection `X_{k'} ⟶ X`. -/
def baseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (toScheme k').obj ((baseChange k k').obj X) ⟶ (toScheme k).obj X :=
  pullback.fst X.obj.hom (ArtinSchreier.specExt k k')

/-- The projections are natural. -/
@[reassoc]
theorem baseChangeProj_naturality {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    (toScheme k').map ((baseChange k k').map f) ≫ baseChangeProj Y =
      baseChangeProj X ≫ (toScheme k).map f :=
  pullback.lift_fst _ _ _

/-- The base change square `X_{k'} → X`, `X_{k'} → Spec k'` is cartesian. -/
theorem isPullback_baseChangeProj (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback (baseChangeProj X) ((baseChange k k').obj X).obj.hom X.obj.hom
      (ArtinSchreier.specExt k k') :=
  IsPullback.of_hasPullback _ _

end Stacks.WeilCohomology.SmoothProjectiveScheme

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The base change of a morphism, the projections and the morphism form a cartesian square. -/
theorem isPullback_baseChange_map {X Z : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ Z) :
    IsPullback ((toScheme k').map ((baseChange k k').map i)) (baseChangeProj X)
      (baseChangeProj Z) ((toScheme k).map i) := by
  refine IsPullback.of_right (h₁₂ := ((baseChange k k').obj Z).obj.hom)
    (h₂₂ := Z.obj.hom) (v₁₃ := ArtinSchreier.specExt k k') ?_ (baseChangeProj_naturality i)
    (isPullback_baseChangeProj Z).flip
  rw [w ((baseChange k k').map i), w i]
  exact (isPullback_baseChangeProj X).flip

/-- The base change of the empty scheme is empty. -/
theorem isEmpty_baseChange {X : (SmoothProjectiveScheme k).FullSubcategory}
    (h : IsEmpty ((toScheme k).obj X)) : IsEmpty ((toScheme k').obj ((baseChange k k').obj X)) :=
  ⟨fun x => h.elim ((baseChangeProj X).base x)⟩

/-- **Base change preserves binary coproducts**: if `i : X → Z`, `j : Y → Z` exhibit `Z` as
`X ⨿ Y`, then `i_{k'}`, `j_{k'}` exhibit `Z_{k'}` as `X_{k'} ⨿ Y_{k'}`. -/
theorem nonempty_isColimit_baseChange {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : Nonempty (IsColimit (BinaryCofan.mk ((toScheme k).map i) ((toScheme k).map j)))) :
    Nonempty (IsColimit (BinaryCofan.mk ((toScheme k').map ((baseChange k k').map i))
      ((toScheme k').map ((baseChange k k').map j)))) := by
  obtain ⟨hc⟩ := h
  exact ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hc)
    (BinaryCofan.mk ((toScheme k').map ((baseChange k k').map i))
      ((toScheme k').map ((baseChange k k').map j)))
    (baseChangeProj X) (baseChangeProj Y) (baseChangeProj Z)
    (baseChangeProj_naturality i).symm (baseChangeProj_naturality j).symm).mpr
    ⟨isPullback_baseChange_map i, isPullback_baseChange_map j⟩

end Stacks.WeilCohomology.SmoothProjectiveScheme
