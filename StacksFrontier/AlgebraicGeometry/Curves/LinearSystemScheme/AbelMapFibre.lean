module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Statement
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeZero.ResidueDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibre of the Abel map over `[𝒪_X(D)]` ([Stacks, Tag 0CCT])

Let `X` be a smooth projective curve over an algebraically closed field `k`, an object of a big
fppf site, and `D ⊆ X` an effective Cartier divisor. The Abel map
`γ_d : Hilb^d_{X/k} → Pic_{X/k}`, `Z ↦ [𝒪(Z)]`, is `AlgebraicGeometry.RigidifiedPicard.familyClass`
followed by the map `Pic(X_T) → Pic_{X/k}(T)` into the Picard functor
`Stacks.PicardFunctor.picardFunctor` of [Stacks, Tag 0B9L]. Its fibre over the point
`[𝒪_X(D)] ∈ Pic_{X/k}(Spec k)` is `Stacks.LinearSystemScheme.abelMapFibre`.

`Stacks.LinearSystemScheme.abelFibre_eq_abelMapFibre` identifies it with
`Stacks.LinearSystemScheme.abelFibre`, the families `Z` with `𝒪(Z)` Zariski-locally isomorphic to
`pr_X^* 𝒪_X(D)`. One direction uses that `Pic_{X/k}` is an fppf sheaf. The other uses exactness of
`Pic(T) → Pic(X_T) → Pic_{X/k}(T)` ([Stacks, Tag 0B9M]; its hypothesis holds for such a curve by
[Stacks, Tag 0B9U]) and the Zariski-local triviality of invertible modules on `T`.

## Main results

* `Stacks.LinearSystemScheme.abelFibre_eq_abelMapFibre`.
* `Stacks.LinearSystemScheme.completeLinearSystem_eq_closedPoints_abelMapFibre`: the fibre of
  `γ_d` is represented by `𝐏(H⁰(X, 𝒪_X(D))^∨)`, whose closed points are the members of `|D|`.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9M](https://stacks.math.columbia.edu/tag/0B9M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.LinearSystemScheme

/-- Isomorphism of the pullbacks of `𝒪(Z)` and `𝒪(D)` is equality of the pulled-back classes. -/
theorem nonempty_iso_pullback_iff {Y W X : Scheme.{u}} (j : Y ⟶ W) (q : Y ⟶ X)
    (Z : W.IdealSheafData) (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Z]
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Nonempty ((Scheme.Modules.pullback j).obj (Stacks.Divisors.modulesInvertibleSheaf Z) ≅
        (Scheme.Modules.pullback q).obj (Stacks.Divisors.modulesInvertibleSheaf D)) ↔
      Stacks.Picard.schemePullbackClass j (Stacks.Divisors.picardClass Z) =
        Stacks.Picard.schemePullbackClass q (Stacks.Divisors.picardClass D) := by
  have h1 := Stacks.Picard.pullbackClass_classOf j.toLRSHom.toShHom
    (Stacks.Divisors.invertibleSheaf' Z) (Stacks.Divisors.isInvertible_invertibleSheaf_picard Z)
  have h2 := Stacks.Picard.pullbackClass_classOf q.toLRSHom.toShHom
    (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)
  show _ ↔ Stacks.Picard.pullbackClass j.toLRSHom.toShHom _ =
    Stacks.Picard.pullbackClass q.toLRSHom.toShHom _
  rw [h1, h2]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).symm

/-- If a class pulls back to zero along `h`, it pulls back to zero along `g ≫ h`. -/
private theorem schemePullbackClass_comp_eq_zero {Y Z W : Scheme.{u}} (g : Y ⟶ Z) (h : Z ⟶ W)
    {x : Stacks.Picard.ofScheme W} (hx : Stacks.Picard.schemePullbackClass h x = 0) :
    Stacks.Picard.schemePullbackClass (g ≫ h) x = 0 := by
  rw [← Stacks.Picard.schemePullbackClass_comp, hx]
  exact map_zero (Stacks.Picard.schemePullbackClassHom _)

section Restriction

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The base change `X_V ⟶ X_T` along the inclusion of `V ⊆ T` commutes with the projections to
`X`. -/
theorem familyBaseChangeMap_restrictHom_fst {T : Over (Spec (.of k))} (V : T.left.Opens) :
    Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι) ≫ pullback.fst f T.hom =
      pullback.fst f (V.ι ≫ T.hom) := by
  simp [Stacks.Hilbert.familyBaseChangeMap]

/-- The base change `X_V ⟶ X_T` along the inclusion of `V ⊆ T`, followed by the projection to `T`,
is the projection to `V` followed by the inclusion `V ⟶ T`. -/
theorem familyBaseChangeMap_restrictHom_snd {T : Over (Spec (.of k))} (V : T.left.Opens) :
    Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι) ≫ pullback.snd f T.hom =
      pullback.snd f (V.ι ≫ T.hom) ≫ V.ι := by
  simp [Stacks.Hilbert.familyBaseChangeMap]

/-- The base change along `w : W ⟶ T` factors through `X_V` when `w` factors through `V`. -/
theorem familyBaseChangeMap_restrictHom_factor {T : Over (Spec (.of k))} (V : T.left.Opens)
    {W : Scheme.{u}} (w : W ⟶ T.left) (e : W ⟶ V) (he : e ≫ V.ι = w) :
    Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom w) =
      pullback.map f (w ≫ T.hom) f (V.ι ≫ T.hom) (𝟙 _) e (𝟙 _) (by simp)
          (by rw [← he, Category.assoc, Category.comp_id, Category.assoc]) ≫
        Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι) := by
  apply pullback.hom_ext <;> simp [Stacks.Hilbert.familyBaseChangeMap, ← he]

/-- Restricting `[𝒪(Z)] - pr_X^*[𝒪(D)]` to `X_V` gives zero exactly when `𝒪(Z)` and
`pr_X^* 𝒪(D)` are isomorphic over `X_V`. -/
theorem nonempty_iso_restrict_iff {T : Over (Spec (.of k))} (V : T.left.Opens)
    (Z : ((Over.pullback T.hom).obj (curveOver f)).left.IdealSheafData) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Z] [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Nonempty ((Scheme.Modules.pullback
        (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))).obj
          (Stacks.Divisors.modulesInvertibleSheaf Z) ≅
      (Scheme.Modules.pullback (pullback.fst f (V.ι ≫ T.hom))).obj
          (Stacks.Divisors.modulesInvertibleSheaf D)) ↔
      Stacks.Picard.schemePullbackClass
        (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))
        (Stacks.Divisors.picardClass Z -
          (Stacks.Picard.schemePullbackClass (pullback.fst f T.hom)
            (Stacks.Divisors.picardClass D) :
              Stacks.Picard.ofScheme ((Over.pullback T.hom).obj (curveOver f)).left)) = 0 := by
  rw [nonempty_iso_pullback_iff, ← sub_eq_zero]
  have h : Stacks.Picard.schemePullbackClass
      (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))
      (Stacks.Divisors.picardClass Z -
        (Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) (Stacks.Divisors.picardClass D) :
          Stacks.Picard.ofScheme ((Over.pullback T.hom).obj (curveOver f)).left)) =
      Stacks.Picard.schemePullbackClass
        (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))
        (Stacks.Divisors.picardClass Z) -
      Stacks.Picard.schemePullbackClass
        (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))
        (Stacks.Picard.schemePullbackClass (pullback.fst f T.hom)
          (Stacks.Divisors.picardClass D)) :=
    (Stacks.Picard.schemePullbackClassHom
      (Stacks.Hilbert.familyBaseChangeMap (curveOver f) (restrictHom V.ι))).map_sub _ _
  rw [h, Stacks.Picard.schemePullbackClass_comp, familyBaseChangeMap_restrictHom_fst]

end Restriction

section Site

open Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (k : Type u) [Field k]
  [IsAlgClosed k] {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)]
  (D : (B.inclusion.obj (B.obj hX)).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The point `[𝒪_X(D)]` of `Pic_{X/k}(Spec k)`: the class of the pullback of `𝒪_X(D)` to
`X ×_k k`. -/
def divisorPoint : (picardFunctor B hX hk g).obj (op (terminalTest B hk)) :=
  toPicardFunctorHom B hX hk g (terminalTest B hk)
    (Stacks.Picard.schemePullbackClass
      (pullback.fst (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom))
      (Stacks.Divisors.picardClass D))

/-- `[𝒪_X(D)]` is the image of the class of `𝒪_X(D)` under `Pic(X) ≃ Pic_{X/k}(Spec k)`. -/
theorem divisorPoint_eq :
    divisorPoint B hX k g D =
      ofSchemeAddEquivPicardFunctorOfCurve B hX k g
        (@Stacks.Divisors.picardClass (B.inclusion.obj (B.obj hX)) D _) :=
  rfl

/-- The structure morphism of a `k`-scheme of the site, as a morphism to the terminal one. -/
abbrev toTerminal (T : BigFppfOver B (Spec (.of k)) hk) : T ⟶ terminalTest B hk :=
  Over.homMk T.hom (by simp)

/-- **The fibre of the Abel map `γ_d : Hilb^d_{X/k} → Pic_{X/k}` over the point `[𝒪_X(D)]`**, at
a `k`-scheme `T` of the site: the degree-`d` Hilbert families `Z ⊆ X_T` whose Abel class
`γ_d(Z) = [𝒪_{X_T}(Z)] ∈ Pic_{X/k}(T)` (`AlgebraicGeometry.RigidifiedPicard.familyClass`) is the
restriction to `T` of `[𝒪_X(D)] ∈ Pic_{X/k}(Spec k)`. This is the value at `T` of the fibre
product `Hilb^d_{X/k} ×_{Pic_{X/k}} Spec k`. -/
def abelMapFibre (d : ℕ) (T : BigFppfOver B (Spec (.of k)) hk) :
    Set (Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T) d) :=
  {Z | toPicardFunctorHom B hX hk g T (RigidifiedPicard.familyClass (B.inclusion.map g) Z) =
    (picardFunctor B hX hk g).map (toTerminal B k T).op (divisorPoint B hX k g D)}

omit [IsAlgClosed k] [IsCurve k (B.inclusion.map g)] [IsProjectiveVariety k (B.inclusion.map g)]
  [Smooth (B.inclusion.map g)] in
/-- The restriction of `[𝒪_X(D)]` to `T` is the class of `pr_X^* 𝒪_X(D)` on `X_T`. -/
theorem map_divisorPoint (T : BigFppfOver B (Spec (.of k)) hk) :
    (picardFunctor B hX hk g).map (toTerminal B k T).op (divisorPoint B hX k g D) =
      toPicardFunctorHom B hX hk g T (Stacks.Picard.schemePullbackClass
        (pullback.fst (B.inclusion.map g) (B.inclusion.map T.hom))
        (Stacks.Divisors.picardClass D)) := by
  refine (toPicardFunctor_app_naturality B hX hk g (toTerminal B k T) _).symm.trans ?_
  rw [toPicardFunctorHom_apply]
  congr 1
  refine (Stacks.Picard.schemePullbackClass_comp _ _ _).trans ?_
  congr 1
  simp [Stacks.PicardFunctor.baseChangeMap]

/-- **The fibre of the Abel map is `abelFibre`.** For a `k`-scheme `T` of the site, a degree-`d`
family `Z ⊆ X_T` lies in the fibre of `γ_d : Hilb^d_{X/k} → Pic_{X/k}` over `[𝒪_X(D)]` exactly
when `𝒪_{X_T}(Z)` is, Zariski locally on `T`, isomorphic to `pr_X^* 𝒪_X(D)`. One direction is the
sheaf property of `Pic_{X/k}`; the other is exactness of `Pic(T) → Pic(X_T) → Pic_{X/k}(T)`
([Stacks, Tag 0B9M], for a curve with a rational point by [Stacks, Tag 0B9U]) together with the
Zariski-local triviality of invertible modules on `T`. -/
theorem abelFibre_eq_abelMapFibre (d : ℕ) (T : BigFppfOver B (Spec (.of k)) hk) :
    abelFibre (B.inclusion.map g) D d ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T) =
      abelMapFibre B hX k g D d T := by
  ext Z
  let : Stacks.Divisors.IsEffectiveCartierDivisor Z.ideal :=
    (RigidifiedPicard.isRelativeEffectiveCartierDivisor_hilbertFamily (B.inclusion.map g) Z).1
  set x : Stacks.Picard.ofScheme
      (pullback (B.inclusion.map g) ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).hom) :=
    RigidifiedPicard.familyClass (B.inclusion.map g) Z -
      Stacks.Picard.schemePullbackClass
        (pullback.fst (B.inclusion.map g) ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).hom)
        (Stacks.Divisors.picardClass D) with hx
  have hiff : Z ∈ abelMapFibre B hX k g D d T ↔ toPicardFunctorHom B hX hk g T x = 0 := by
    show _ = _ ↔ _
    rw [map_divisorPoint, ← sub_eq_zero, hx]
    exact iff_of_eq (congrArg (· = 0) ((toPicardFunctorHom B hX hk g T).map_sub _ _).symm)
  rw [hiff]
  constructor
  · intro hZ
    choose V hVa htV hVi using hZ
    let 𝒰 : (B.inclusion.obj T.left).OpenCover :=
      (B.inclusion.obj T.left).openCoverOfIsOpenCover V (eq_top_iff.mpr fun t _ =>
        TopologicalSpace.Opens.mem_iSup.mpr ⟨t, htV t⟩)
    obtain ⟨W, hW, hequiv⟩ :=
      AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_openCover B T.left 𝒰
    obtain ⟨β, hβ⟩ := hequiv.2
    have hloc : ∀ i, picardMap B hX hk g
        (Over.homMk (U := Over.mk (W.f i ≫ T.hom)) (V := T) (W.f i)) x = 0 := by
      intro i
      obtain ⟨e, he⟩ := hβ i
      have hrest := (nonempty_iso_restrict_iff (B.inclusion.map g) (V (β i)) Z.ideal
        D).1 (hVi (β i))
      have he' : e.hom ≫ (V (β i)).ι = B.inclusion.map (W.f i) := he
      show Stacks.Picard.schemePullbackClass (Stacks.Hilbert.familyBaseChangeMap
        (curveOver (B.inclusion.map g))
        (restrictHom (T := (BigFppfOver.toOver B (Spec (.of k)) hk).obj T)
          (B.inclusion.map (W.f i)))) x = 0
      refine (congrArg (fun m => Stacks.Picard.schemePullbackClass m x)
        (familyBaseChangeMap_restrictHom_factor _ (V (β i)) _ e.hom he')).trans ?_
      exact schemePullbackClass_comp_eq_zero _ _ hrest
    have hg : Sieve.ofArrows (fun i : W.I₀ => (Over.mk (W.f i ≫ T.hom) :
        BigFppfOver B (Spec (.of k)) hk)) (fun i => Over.homMk (W.f i)) ∈
          BigFppfOver.topology B (Spec (.of k)) hk T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact Precoverage.generate_mem_toGrothendieck ⟨W, rfl, hW⟩
    have heq : (TypeCat.ofHom (fun _ : PUnit.{u + 2} => toPicardFunctorHom B hX hk g T x)) =
        TypeCat.ofHom (fun _ : PUnit.{u + 2} => toPicardFunctorHom B hX hk g T 0) := by
      apply (isSheaf_picardFunctor B hX hk g).hom_ext_ofArrows
        (X := fun i : W.I₀ => (Over.mk (W.f i ≫ T.hom) : BigFppfOver B (Spec (.of k)) hk))
        (fun i => Over.homMk (W.f i)) hg
      intro i
      ext z
      refine (toPicardFunctor_app_naturality B hX hk g _ x).symm.trans
        (Eq.trans ?_ (toPicardFunctor_app_naturality B hX hk g _ 0))
      rw [hloc i]
      exact congrArg _ (map_zero (picardMapHom B hX hk g _)).symm
    exact (ConcreteCategory.congr_hom heq PUnit.unit).trans
      (map_zero (toPicardFunctorHom B hX hk g T))
  · intro h0 t
    obtain ⟨N, hN⟩ := (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom_of_isIso_c
      B hX hk g (isIso_c_baseChangeProj_of_curve B hX k g) T x).1 h0
    obtain ⟨𝒰, h𝒰⟩ := Stacks.Picard.exists_openCover_schemePullbackClass_eq_zero N
    obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVU⟩ :=
      (B.inclusion.obj T.left).isBasis_affineOpens.exists_subset_of_mem_open (𝒰.covers t)
        (𝒰.f (𝒰.idx t)).opensRange.2
    refine ⟨V, hV, htV, ?_⟩
    refine (nonempty_iso_restrict_iff (T := (BigFppfOver.toOver B (Spec (.of k)) hk).obj T)
      (B.inclusion.map g) V Z.ideal D).2 ?_
    show Stacks.Picard.schemePullbackClass _ x = 0
    refine (congrArg (Stacks.Picard.schemePullbackClass _) hN.symm).trans ?_
    refine (Stacks.Picard.schemePullbackClass_comp _ _ N).trans ?_
    refine (congrArg (fun m => Stacks.Picard.schemePullbackClass m N)
      (familyBaseChangeMap_restrictHom_snd (B.inclusion.map g)
        (T := (BigFppfOver.toOver B (Spec (.of k)) hk).obj T) V)).trans ?_
    have hV0 : Stacks.Picard.schemePullbackClass (Scheme.Opens.ι V) N = 0 := by
      rw [← IsOpenImmersion.lift_fac (𝒰.f (𝒰.idx t)) (Scheme.Opens.ι V)
          (by rwa [Scheme.Opens.range_ι])]
      exact schemePullbackClass_comp_eq_zero _ _ (h𝒰 _)
    exact schemePullbackClass_comp_eq_zero _ _ hV0

/-- **Stacks Project, Tag 0CCT.** Let `X` be a smooth projective curve over an algebraically
closed field `k` and `D ⊆ X` an effective Cartier divisor of degree `d`. The fibre
`Hilb^d_{X/k} ×_{Pic_{X/k}} Spec k` of the Abel map `γ_d : Hilb^d_{X/k} → Pic_{X/k}`,
`Z ↦ [𝒪(Z)]` (`AlgebraicGeometry.RigidifiedPicard.familyClass`), over the point `[𝒪_X(D)]` is
represented by `𝐏(H⁰(X, 𝒪_X(D))^∨)`: its `T`-points are naturally the `k`-morphisms
`T ⟶ 𝐏(H⁰(X, 𝒪_X(D))^∨)`. The closed points of this scheme are exactly the members of `|D|`, a
closed point corresponding to the image in `X` of the family over `Spec k` it classifies; the
closed point cut out by evaluation at a nonzero `s ∈ H⁰(X, 𝒪_X(D))` corresponds to the zero
scheme `Z(s)`. This is the scheme structure on `|D|`. -/
@[stacks 0CCT "|D| is the set of closed points of the fibre of gamma_d : Hilb^d -> Pic over the \
point of O_X(D); this gives |D| a natural scheme structure"]
theorem completeLinearSystem_eq_closedPoints_abelMapFibre {d : ℕ}
    (hd : invertibleCurveDegree k (B.inclusion.map g)
      (topologicalKrullDim_le_one k (B.inclusion.map g))
      (Stacks.Divisors.modulesInvertibleSheaf D) = d) :
    ∃ e : ∀ T : BigFppfOver B (Spec (.of k)) hk,
        ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶
          (linearSystemScheme k (B.inclusion.map g) D).asOver (Spec (.of k))) ≃
          abelMapFibre B hX k g D d T,
      (∀ (T T' : BigFppfOver B (Spec (.of k)) hk) (h : T' ⟶ T)
          (p : (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶
            (linearSystemScheme k (B.inclusion.map g) D).asOver (Spec (.of k))),
        (e T' ((BigFppfOver.toOver B (Spec (.of k)) hk).map h ≫ p)).1.ideal =
          (e T p).1.ideal.comap (Stacks.Hilbert.familyBaseChangeMap
            (curveOver (B.inclusion.map g)) ((BigFppfOver.toOver B (Spec (.of k)) hk).map h))) ∧
      ∃ c : closedPoints (linearSystemScheme k (B.inclusion.map g) D) ≃
          Stacks.Divisors.completeLinearSystem D,
        (∀ x : closedPoints (linearSystemScheme k (B.inclusion.map g) D),
          (c x : (B.inclusion.obj (B.obj hX)).IdealSheafData) =
            (e (terminalTest B hk) (Over.homMk (@pointOfClosedPoint _ _ _ _
              (projectiveSpaceOfModuleToSpec k (dualSections k (B.inclusion.map g) D))
              (locallyOfFiniteType_linearSystemScheme k (B.inclusion.map g) D) x.1 x.2)
              (@pointOfClosedPoint_comp _ _ _ _ _
                (locallyOfFiniteType_linearSystemScheme k (B.inclusion.map g) D) x.1
                x.2))).1.ideal.comap
              (baseChangeTerminalIso B hX hk g).inv) ∧
        ∀ (s : cohomologyOverField k (B.inclusion.map g)
            (Stacks.Divisors.modulesInvertibleSheaf D) 0) (hs : s ≠ 0),
          (c ⟨ProjectiveSpaceOfModule.linearFunctionalPoint k _ (Module.Dual.eval k _ s)
              (eval_ne_zero k (B.inclusion.map g) D hs),
            ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed k _ _
              (eval_ne_zero k (B.inclusion.map g) D hs)⟩ :
              (B.inclusion.obj (B.obj hX)).IdealSheafData) =
            zeroScheme _ (Stacks.Divisors.modulesInvertibleSheaf D)
              (sectionOf k (B.inclusion.map g) (Stacks.Divisors.modulesInvertibleSheaf D) s) := by
  obtain ⟨e₀, he₀, c, hc, hpin⟩ := completeLinearSystem_eq_closedPoints_abelFibre k
    (B.inclusion.map g) D hd
  refine ⟨fun T => (e₀ _).trans (Equiv.subtypeEquivRight fun Z => by
      rw [abelFibre_eq_abelMapFibre B hX k g D d T]),
    fun T T' h p => he₀ _ _ _ p, c, hc, hpin⟩

end Site

end Stacks.LinearSystemScheme

end
