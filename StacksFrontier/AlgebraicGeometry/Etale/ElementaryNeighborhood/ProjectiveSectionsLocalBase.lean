module

public import Mathlib.Algebra.Module.Projective
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectiveSectionsAffineOpen05ME
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Projective sections over the local ring of an elementary étale neighbourhood

Stacks Tag 05ME produces, for `f : X ⟶ S` locally of finite presentation and `F` a quasi-coherent
`𝒪_X`-module of finite presentation which is flat over `S` at `x`, an affine elementary étale
neighbourhood `(S', s')` of `(S, f x)` and an affine open `U' ⊆ X ×_S S'` containing `x'` whose
sections are projective over `Γ(S', 𝒪_{S'})`.

Stacks Tag 05MF asks for the same data over the *local scheme* `Spec 𝒪_{S', s'}` instead of over
`S'`, with the sections projective (then free) over the local ring `𝒪_{S', s'}`. This file is the
passage between the two: base change along `Spec 𝒪_{S', s'} ⟶ S'`.

The base change is harmless because everything in sight is affine. The square

```
X ×_S Spec 𝒪_{S', s'} ⟶ X ×_S S'
         |                   |
         v                   v
   Spec 𝒪_{S', s'}    ⟶     S'
```

is cartesian, so the preimage `W` of `U'` is again affine and its ring of sections is
`Γ(U') ⊗_{Γ(S')} 𝒪_{S', s'}` (`AlgebraicGeometry.IsAffineOpen.inf_preimage_of_isPullback` and
`AlgebraicGeometry.algebra_isPushout_appLE_of_isPullback`); the sections of the pulled back module
over `W` are correspondingly the base change of the sections over `U'`
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), and a base change of a projective module
is projective.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.exists_affineOpen_projective_sections_stalk`: Tag 05ME transported to the
  local scheme of the neighbourhood it produces. This is the conclusion of Tag 05MF with
  `Module.Projective` in place of `Module.Free`, under the finite-presentation hypotheses of
  Tag 05ME.

## Implementation notes

The conclusion is stated in exactly the shape in which Tag 05MF consumes it, so that it can be
handed to `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_free_sections` unchanged: the
scalar action on the sections is restriction along the second pullback projection composed with
the canonical identification of the local ring with the global sections of its spectrum.

The open `W` is written as `c ⁻¹ᵁ U' ⊓ q ⁻¹ᵁ ⊤` rather than as `c ⁻¹ᵁ U'`, which is the same open,
because that is the shape in which `AlgebraicGeometry.IsAffineOpen.inf_preimage_of_isPullback` and
`AlgebraicGeometry.algebra_isPushout_appLE_of_isPullback` state their conclusions, and writing it
that way lets both apply with `rfl`.

## References

* [Stacks Project, Tag 05ME](https://stacks.math.columbia.edu/tag/05ME)
* [Stacks Project, Tag 05MF](https://stacks.math.columbia.edu/tag/05MF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **A base change of a projective module is projective**, read on a pushout square of rings: if
`M` is projective over `R` and `T` is the pushout of `A` and `B` over `R`, then `T ⊗[A] M` is
projective over `B`. -/
private theorem projective_of_projective_pushout
    {R A B T M : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] [Algebra A T] [Algebra B T]
    [IsScalarTower R A T] [IsScalarTower R B T] [Algebra.IsPushout R B A T]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.Projective R M] :
    Module.Projective B (T ⊗[A] M) := by
  have : Module.Projective B (B ⊗[R] M) := inferInstance
  exact Module.Projective.of_equiv (Algebra.IsPushout.cancelBaseChange R B A T M).symm

/-- **An affine open with projective sections survives an affine base change.** Let `f : X ⟶ S`
be a morphism, let `F` be a quasi-coherent `𝒪_X`-module, let `b : Y ⟶ S` have affine source and
let `ρ : T ⟶ Y` have affine source. Suppose `U'` is an affine open of `X ×_S Y` containing a point
`x₁` over `x` and over `ρ t`, and that the sections of the pullback of `F` over `U'` are a
projective `Γ(Y, 𝒪_Y)`-module. Then the preimage of `U'` in `X ×_S T` is an affine open containing
a point over `x` and over `t`, and its sections are a projective `Γ(T, 𝒪_T)`-module.

The square with corners `X ×_S T`, `X ×_S Y`, `T` and `Y` is cartesian, so the preimage is affine
and its ring of sections is `Γ(X ×_S Y, U') ⊗_{Γ(Y, ⊤)} Γ(T, ⊤)`; the sections of the pulled back
module are the corresponding base change, and a base change of a projective module is
projective. -/
theorem exists_affineOpen_projective_sections_baseChange
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (b : Y ⟶ S) (ρ : T ⟶ Y) [IsAffine Y] [IsAffine T]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) (t : T)
    (x₁ : (pullback f b : Scheme.{u})) (hx₁fst : pullback.fst f b x₁ = x)
    (hx₁snd : pullback.snd f b x₁ = ρ t)
    (U' : (pullback f b : Scheme.{u}).Opens) (hU'aff : IsAffineOpen U') (hx₁U' : x₁ ∈ U')
    (hproj :
      letI : Module Γ(Y, ⊤) Γ((Scheme.Modules.pullback (pullback.fst f b)).obj F, U') :=
        Module.compHom _ ((pullback.snd f b).appLE ⊤ U' (by simp)).hom
      Module.Projective Γ(Y, ⊤) Γ((Scheme.Modules.pullback (pullback.fst f b)).obj F, U')) :
    ∃ (x' : (pullback f (ρ ≫ b) : Scheme.{u}))
      (W : (pullback f (ρ ≫ b) : Scheme.{u}).Opens),
      pullback.fst f (ρ ≫ b) x' = x ∧ pullback.snd f (ρ ≫ b) x' = t ∧
        IsAffineOpen W ∧ x' ∈ W ∧
          letI : Module Γ(T, ⊤)
              Γ((Scheme.Modules.pullback (pullback.fst f (ρ ≫ b))).obj F, W) :=
            Module.compHom _ ((pullback.snd f (ρ ≫ b)).appLE ⊤ W (by simp)).hom
          Module.Projective Γ(T, ⊤)
            Γ((Scheme.Modules.pullback (pullback.fst f (ρ ≫ b))).obj F, W) := by
  set r : (pullback f b : Scheme.{u}) ⟶ Y := pullback.snd f b
  set q : (pullback f (ρ ≫ b) : Scheme.{u}) ⟶ T := pullback.snd f (ρ ≫ b)
  -- the comparison `X ×_S T ⟶ X ×_S Y` and the cartesian square it sits in
  set c : (pullback f (ρ ≫ b) : Scheme.{u}) ⟶ (pullback f b : Scheme.{u}) :=
    pullback.lift (pullback.fst f (ρ ≫ b)) (q ≫ ρ)
      (by rw [Category.assoc]; exact pullback.condition)
  have hcfst : c ≫ pullback.fst f b = pullback.fst f (ρ ≫ b) := pullback.lift_fst _ _ _
  have hcsnd : c ≫ r = q ≫ ρ := pullback.lift_snd _ _ _
  set e := pullbackLeftPullbackSndIso f b ρ
  have hefst : e.hom ≫ pullback.fst f (ρ ≫ b) = pullback.fst r ρ ≫ pullback.fst f b :=
    pullbackLeftPullbackSndIso_hom_fst f b ρ
  have hesnd : e.hom ≫ q = pullback.snd r ρ := pullbackLeftPullbackSndIso_hom_snd f b ρ
  have heinvsnd : e.inv ≫ pullback.snd r ρ = q := by rw [← hesnd, Iso.inv_hom_id_assoc]
  have heinvfst : e.inv ≫ pullback.fst r ρ = c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, ← hefst, Iso.inv_hom_id_assoc, hcfst]
    · rw [Category.assoc, pullback.condition, ← Category.assoc, heinvsnd, hcsnd]
  have hPB : IsPullback c q r ρ :=
    IsPullback.of_iso_pullback ⟨hcsnd⟩ e.symm heinvfst heinvsnd
  -- the point of `X ×_S T` over `x` and over `t`
  obtain ⟨z, hzfst, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := r) (g := ρ) x₁ t hx₁snd
  have hxz : pullback.fst f (ρ ≫ b) (e.hom z) = x := by
    rw [← Scheme.Hom.comp_apply, hefst, Scheme.Hom.comp_apply, hzfst, hx₁fst]
  have htz : q (e.hom z) = t := by
    rw [← Scheme.Hom.comp_apply, hesnd, hzsnd]
  have hcz : c (e.hom z) = x₁ := by
    rw [← heinvfst, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.hom e.inv]
    simp [hzfst]
  -- the affine open and the three ring maps of the pushout square
  have hUle : U' ≤ r ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hTle : (⊤ : T.Opens) ≤ ρ ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  set W : (pullback f (ρ ≫ b) : Scheme.{u}).Opens := c ⁻¹ᵁ U' ⊓ q ⁻¹ᵁ ⊤ with hW
  have hWle : W ≤ c ⁻¹ᵁ U' := inf_le_left
  have hWleT : W ≤ q ⁻¹ᵁ (⊤ : T.Opens) := inf_le_right
  have hWaff : IsAffineOpen W :=
    IsAffineOpen.inf_preimage_of_isPullback hPB (isAffineOpen_top Y) hU'aff hUle
      (isAffineOpen_top T) hTle rfl
  refine ⟨e.hom z, W, hxz, htz, hWaff, ⟨by rw [hW]; exact ⟨by simpa [hcz] using hx₁U', trivial⟩,
    ?_⟩⟩
  -- the algebra of the pushout square
  let : Algebra Γ(Y, ⊤) Γ((pullback f b : Scheme.{u}), U') := (r.appLE ⊤ U' hUle).hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(T, ⊤) := (ρ.appLE ⊤ ⊤ hTle).hom.toAlgebra
  let : Algebra Γ((pullback f b : Scheme.{u}), U') Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    (c.appLE U' W hWle).hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    (q.appLE ⊤ W hWleT).hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    (r.appLE ⊤ U' hUle ≫ c.appLE U' W hWle).hom.toAlgebra
  have hw := (isPushout_appLE_of_isPullback hPB (isAffineOpen_top Y) hU'aff hUle
    (isAffineOpen_top T) hTle rfl).w
  have : IsScalarTower Γ(Y, ⊤) Γ((pullback f b : Scheme.{u}), U')
      Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, ⊤) Γ(T, ⊤) Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    .of_algebraMap_eq' congr($(hw).hom)
  have : Algebra.IsPushout Γ(Y, ⊤) Γ(T, ⊤) Γ((pullback f b : Scheme.{u}), U')
      Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    algebra_isPushout_appLE_of_isPullback hPB (isAffineOpen_top Y) hU'aff hUle
      (isAffineOpen_top T) hTle rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  -- the module of sections upstairs is the base change of the projective one downstairs
  set G := (Scheme.Modules.pullback (pullback.fst f b)).obj F
  have : G.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F
  let : Module Γ(Y, ⊤) Γ(G, U') := Module.compHom _ (r.appLE ⊤ U' hUle).hom
  have : IsScalarTower Γ(Y, ⊤) Γ((pullback f b : Scheme.{u}), U') Γ(G, U') :=
    ⟨fun a a' m => mul_smul ((r.appLE ⊤ U' hUle).hom a) a' m⟩
  have : Module.Projective Γ(Y, ⊤) Γ(G, U') := hproj
  have hTensor : Module.Projective Γ(T, ⊤)
      (Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) ⊗[Γ((pullback f b : Scheme.{u}), U')]
        Γ(G, U')) :=
    projective_of_projective_pushout (R := Γ(Y, ⊤))
      (A := Γ((pullback f b : Scheme.{u}), U')) (B := Γ(T, ⊤))
      (T := Γ((pullback f (ρ ≫ b) : Scheme.{u}), W)) (M := Γ(G, U'))
  let : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback c).obj G, W) :=
    Module.compHom _ (q.appLE ⊤ W hWleT).hom
  let : Module Γ(T, ⊤) Γ((Scheme.Modules.pullback (pullback.fst f (ρ ≫ b))).obj F, W) :=
    Module.compHom _ (q.appLE ⊤ W hWleT).hom
  let : LinearMap.CompatibleSMul
      (Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) ⊗[Γ((pullback f b : Scheme.{u}), U')] Γ(G, U'))
      Γ((Scheme.Modules.pullback c).obj G, W) Γ(T, ⊤)
      Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    ⟨fun k a m => k.map_smul ((q.appLE ⊤ W hWleT).hom a) m⟩
  have eAff : Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) ⊗[Γ((pullback f b : Scheme.{u}), U')]
        Γ(G, U') ≃ₗ[Γ((pullback f (ρ ≫ b) : Scheme.{u}), W)]
      Γ((Scheme.Modules.pullback c).obj G, W) :=
    (affinePullbackSectionsBaseChangeIso c G hU'aff hWaff hWle).toLinearEquiv
  have hSections : Module.Projective Γ(T, ⊤) Γ((Scheme.Modules.pullback c).obj G, W) :=
    Module.Projective.of_equiv (eAff.restrictScalars Γ(T, ⊤))
  -- and the pullback along `c` of `G` is the pullback of `F` to `X ×_S T`
  let : LinearMap.CompatibleSMul Γ((Scheme.Modules.pullback c).obj G, W)
      Γ((Scheme.Modules.pullback (pullback.fst f (ρ ≫ b))).obj F, W) Γ(T, ⊤)
      Γ((pullback f (ρ ≫ b) : Scheme.{u}), W) :=
    ⟨fun k a m => k.map_smul ((q.appLE ⊤ W hWleT).hom a) m⟩
  have E : (Scheme.Modules.pullback c).obj G ≅
      (Scheme.Modules.pullback (pullback.fst f (ρ ≫ b))).obj F :=
    (Scheme.Modules.pullbackComp c (pullback.fst f b)).app F ≪≫
      (Scheme.Modules.pullbackCongr hcfst).app F
  exact Module.Projective.of_equiv ((sectionsLinearEquivOfIso E W).restrictScalars Γ(T, ⊤))

/-- **Stacks Project, Tag 05ME over the local scheme of the neighbourhood it produces.** For
`f : X ⟶ S` locally of finite presentation, `F` a quasi-coherent `𝒪_X`-module of finite
presentation and `x : X` at which `F` is flat over `S`, there are an affine elementary étale
neighbourhood `(S', s')` of `(S, f x)` and an affine open `W` of `X ×_S Spec 𝒪_{S', s'}`
containing a point over `x` whose sections are a projective `𝒪_{S', s'}`-module.

This is Tag 05ME base changed along `Spec 𝒪_{S', s'} ⟶ S'`: the open `W` is the preimage of the
affine open `U'` of `X ×_S S'` that Tag 05ME produces, and its sections are
`Γ(U') ⊗_{Γ(S', 𝒪_{S'})} 𝒪_{S', s'}`. -/
theorem exists_affineOpen_projective_sections_stalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (N : EtaleNeighborhood S (f x)),
      N.IsElementary ∧ IsAffine N.scheme ∧
        let g := N.scheme.fromSpecStalk N.point ≫ N.toBase
        let P := pullback f g
        ∃ (x' : P) (W : P.Opens),
          pullback.fst f g x' = x ∧
            IsAffineOpen W ∧ x' ∈ W ∧
              let F' := (Scheme.Modules.pullback (pullback.fst f g)).obj F
              letI : Module (N.scheme.presheaf.stalk N.point) Γ(F', W) :=
                Module.compHom Γ(F', W)
                  (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
                    (pullback.snd f g).appLE ⊤ W (by simp)).hom)
              Module.Projective (N.scheme.presheaf.stalk N.point) Γ(F', W) := by
  obtain ⟨N, hNelem, hNaff, x₁, hx₁fst, hx₁snd, U', hU'aff, hx₁U', hprojME⟩ :=
    exists_affineOpen_projective_sections_of_chart f F (f x) x rfl hflat
  refine ⟨N, hNelem, hNaff, ?_⟩
  have hNaff' : IsAffine N.scheme := hNaff
  obtain ⟨x', W, hx'fst, hx'snd, hWaff, hx'W, hprojW⟩ :=
    exists_affineOpen_projective_sections_baseChange f N.toBase
      (N.scheme.fromSpecStalk N.point) F x
      (IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point))
      x₁ hx₁fst (by rw [hx₁snd, Scheme.fromSpecStalk_closedPoint]) U' hU'aff hx₁U' hprojME
  refine ⟨x', W, hx'fst, hWaff, hx'W, ?_⟩
  -- transport the scalars from `Γ(Spec 𝒪_{S', s'}, ⊤)` to the local ring `𝒪_{S', s'}` itself
  let : Module Γ(Spec (N.scheme.presheaf.stalk N.point), ⊤)
      Γ((Scheme.Modules.pullback
        (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase))).obj F, W) :=
    Module.compHom _
      ((pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase)).appLE ⊤ W (by simp)).hom
  have : Module.Projective Γ(Spec (N.scheme.presheaf.stalk N.point), ⊤)
      Γ((Scheme.Modules.pullback
        (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase))).obj F, W) := hprojW
  let : Module (N.scheme.presheaf.stalk N.point)
      Γ((Scheme.Modules.pullback
        (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase))).obj F, W) :=
    Module.compHom _
      (((Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).inv ≫
        (pullback.snd f (N.scheme.fromSpecStalk N.point ≫ N.toBase)).appLE ⊤ W (by simp)).hom)
  set σ : (N.scheme.presheaf.stalk N.point : Type u) ≃+*
      (Γ(Spec (N.scheme.presheaf.stalk N.point), ⊤) : Type u) :=
    (Scheme.ΓSpecIso (.of (N.scheme.presheaf.stalk N.point))).symm.commRingCatIsoToRingEquiv
  let : RingHomInvPair σ.toRingHom σ.symm.toRingHom := ⟨σ.symm_comp, σ.comp_symm⟩
  let : RingHomInvPair σ.symm.toRingHom σ.toRingHom := ⟨σ.comp_symm, σ.symm_comp⟩
  exact Module.Projective.of_equiv
    (({ toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      Γ((Scheme.Modules.pullback
          (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase))).obj F, W) ≃ₛₗ[σ.toRingHom]
        Γ((Scheme.Modules.pullback
          (pullback.fst f (N.scheme.fromSpecStalk N.point ≫ N.toBase))).obj F, W)).symm)

end AlgebraicGeometry

end
