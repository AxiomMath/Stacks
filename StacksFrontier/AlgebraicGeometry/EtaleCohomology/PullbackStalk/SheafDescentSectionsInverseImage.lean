module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SmallEtaleSheafAdjPseudofunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections of `π_S⁻¹F` and descent for the explicit small étale pseudofunctor

`AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_isEquivalence` deduces the sheaf
condition of `π_S⁻¹F` along one arrow from effective descent for the base's pullback system
`AlgebraicGeometry.smallEtaleSheafPullbackSystem`, which is chosen by `Classical.choice`. Effective
descent along proper surjections (Stacks 0GF0) is proved for the explicit pseudofunctor
`AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`. Here the argument is stated for an
arbitrary small étale sheaf pullback system, the explicit pseudofunctor is packaged as one, and
the sheaf condition is deduced from descent for it.

## Main results

* `AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_system_isEquivalence` — the
  sheaf condition along one arrow from effective descent for any pullback system.
* `AlgebraicGeometry.smallEtaleSheafInverseImagePullbackSystem` — the explicit pseudofunctor as a
  pullback system.
* `AlgebraicGeometry.isSheafFor_smallEtaleInverseImage_singleton_of_inverseImageDescent` — the
  sheaf condition along one arrow from effective descent for the explicit pseudofunctor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **Descent gives the sheaf condition along one arrow, for any pullback system.** If the descent
functor of a small étale sheaf pullback system along `h.left` is an equivalence, then `π_S⁻¹F`
satisfies the sheaf condition for the single arrow `h : X' ⟶ X` of the big étale category over
`S`. Only full faithfulness of the descent functor is used. -/
public theorem isSheafFor_smallEtaleInverseImage_singleton_of_system_isEquivalence
    (Sys : SmallEtaleSheafPullbackSystem B) (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {X X' : BigEtaleOver B S.obj S.property} (h : X' ⟶ X)
    (hG : (Sys.pseudofunctor.toDescentData (fun _ : Unit ↦ h.left)).IsEquivalence) :
    Presieve.IsSheafFor ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj
      (Presieve.singleton h) := by
  let P := Sys.pseudofunctor
  let ES := (eqToHom (Sys.fiber S).symm).toFunctor
  let M := (P.map X.hom.op.toLoc).toFunctor.obj
    (ES.obj (⊤_ Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))))
  let N := (P.map X.hom.op.toLoc).toFunctor.obj (ES.obj F)
  have h1 := (Pseudofunctor.bijective_toDescentData_map_iff (fun _ : Unit ↦ h.left) M N).1
    ((Functor.FullyFaithful.ofFullyFaithful _).map_bijective M N)
  rw [← Presieve.isSheafFor_iff_of_iso (P.overMapCompPresheafHomIso _ _ X.hom),
    Presieve.isSheafFor_iff_generate,
    Presieve.isSheafFor_over_map_op_comp_iff X.hom _ _
      (Over.isoMk (Iso.refl _) (by simp) : (Over.map X.hom).obj (Over.mk (𝟙 X.left)) ≅ X)] at h1
  obtain ⟨ψ⟩ := nonempty_presheafHom_iso B Sys S F
  rw [Presieve.isSheafFor_iff_of_iso ψ] at h1
  rw [Presieve.isSheafFor_iff_generate]
  convert h1 using 2
  apply le_antisymm
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨Over.mk h.left, Over.homMk h.left (by simp),
      Over.homMk (𝟙 X'.left) (by simp [Over.w h]),
      ⟨_, 𝟙 _, _, Presieve.ofArrows.mk (), by simp⟩, ?_⟩
    apply Over.OverMorphism.ext
    simp
  · rintro Z k ⟨W, a, b, ⟨V, c, d, hd, rfl⟩, hab⟩
    obtain ⟨⟩ := hd
    refine ⟨_, b ≫ (Over.map X.hom).map c ≫ Over.homMk (𝟙 X'.left) (by simp [Over.w h]), h,
      Presieve.singleton.mk, ?_⟩
    have := congrArg CommaMorphism.left hab
    apply Over.OverMorphism.ext
    simpa using this.symm

/-- The explicit pseudofunctor of small étale sheaves and their inverse images,
`AlgebraicGeometry.smallEtaleSheafInverseImagePseudofunctor`, as a small étale sheaf pullback
system: its fibres and transition functors are the sheaf categories and the sheaf inverse images
by definition. -/
@[sga "4 VIII 3.4" "more general"]
public def smallEtaleSheafInverseImagePullbackSystem : SmallEtaleSheafPullbackSystem B :=
  ⟨smallEtaleSheafInverseImagePseudofunctor B, fun _ => rfl, fun _ => rfl,
    by intro X Y Z f g; rfl⟩

/-- **Descent for the explicit pseudofunctor gives the sheaf condition along one arrow.** If the
descent functor `AlgebraicGeometry.smallEtaleSheafInverseImageDescentFunctor` along `h.left` is an
equivalence, then `π_S⁻¹F` satisfies the sheaf condition for the single arrow `h : X' ⟶ X` of the
big étale category over `S`. -/
public theorem isSheafFor_smallEtaleInverseImage_singleton_of_inverseImageDescent (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {X X' : BigEtaleOver B S.obj S.property} (h : X' ⟶ X)
    (hdesc : (smallEtaleSheafInverseImageDescentFunctor B h.left).IsEquivalence) :
    Presieve.IsSheafFor ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj
      (Presieve.singleton h) :=
  isSheafFor_smallEtaleInverseImage_singleton_of_system_isEquivalence B
    (smallEtaleSheafInverseImagePullbackSystem B) S F h hdesc

end AlgebraicGeometry

end
