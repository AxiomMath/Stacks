module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.EffectiveDivisors
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.Geometry.HilbertSchemeGeometry
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.Varieties.BoundedDegree.Rank

/-!
# The Abel map into a scheme representing the Picard functor of a curve

Let `X` be a smooth curve over a field `k`, let `P` be an object of a big fppf site representing
the Picard functor `Pic_{X/k}` of [Stacks, Tag 0B9L], and let `H` represent the Hilbert functor
`Hilb^d_{X/k}`, with universal family `D_univ ⊆ X ×_k H`. A degree-`d` Hilbert family of a smooth
curve is a relative effective Cartier divisor ([Stacks, Tag 0B9D]), so `𝒪(D_univ)` is an
invertible module on `X ×_k H`, and by the Yoneda lemma its class is a morphism

`γ_d : H ⟶ P`,

the morphism of [Stacks, Tag 0BA0] (4). Its composite with `m : T ⟶ H` is the class of `𝒪(Z_m)`,
`Z_m` the family classified by `m` ([Stacks, Tag 0C4U]).

On `k`-points, for `k` algebraically closed and `X` proper: every class of `Pic(X)` of degree at
least the genus is `[𝒪_X(D)]` for an effective Cartier divisor `D` finite locally free of rank
`d = deg` over `k`, that is, a `k`-point of `Hilb^d_{X/k}`. Hence every `k`-point of `P` whose
class has degree `d ≥ g` is `γ_d` of a `k`-point of `H`: the surjectivity half of
[Stacks, Tag 0BA0] (5) on rational points.

The class `[𝒪(Z)]` of a Hilbert family is jac-sym's functor-level Abel map
`AlgebraicGeometry.RigidifiedPicard.familyClass` (`Picard/SymmetricPower/AbelMap.lean`).

## Main definitions

* `Stacks.PicardFunctor.abelMap`: the morphism `γ_d : H ⟶ P`.

## Main results

* `Stacks.PicardFunctor.homEquiv_comp_abelMap`: `m ≫ γ_d` is the class of `𝒪(Z_m)`.
* `Stacks.PicardFunctor.exists_comp_abelMap_eq`: every class of `Pic(X)` of degree `d ≥ g` is
  `γ_d` of a `k`-point of `H`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

universe u

namespace Stacks.Divisors

/-- **Finite local freeness of the subscheme of an inverse image along an isomorphism.** If the
subscheme cut out by `I` is finite locally free of rank `d` over `S` via `q`, so is the subscheme
cut out by the inverse image of `I` along an isomorphism `φ`, via `φ ≫ q`. -/
theorem isFiniteLocallyFreeOfRank_comap_of_isIso {Y Y' S : Scheme.{u}} (φ : Y' ⟶ Y) [IsIso φ]
    (q : Y ⟶ S) (I : Y.IdealSheafData) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ q) d] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.comap φ).subschemeι ≫ φ ≫ q) d := by
  have h : (I.comap φ).subschemeι ≫ φ ≫ q =
      ((I.comapIso φ).hom ≫ pullback.snd φ I.subschemeι) ≫ (I.subschemeι ≫ q) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      pullback.condition_assoc]
  rw [h]
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isIso_comp _ _ d

end Stacks.Divisors

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {k : Type u} [Field k]
  {hk : B.Contains (Spec (.of k))} (g : B.obj hX ⟶ B.obj hk)

variable [IsCurve k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

/-- **The pullback of the universal class along `m : T ⟶ H` is the class of the family classified
by `m`** ([Stacks, Tag 0C4U] and the naturality of the universal family). -/
theorem picardMap_familyClass {H : BigFppfOver B (Spec (.of k)) hk} {d : ℕ}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d)
    {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ H) :
    picardMap B hX hk g m (RigidifiedPicard.familyClass (B.inclusion.map g) (hH.family (𝟙 _))) =
      RigidifiedPicard.familyClass (B.inclusion.map g)
        (hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map m)) := by
  have h := hH.naturality ((BigFppfOver.toOver B (Spec (.of k)) hk).map m) (𝟙 _)
  rw [Category.comp_id] at h
  exact @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _
    (baseChangeMap B hX hk g m) _ _
    (RigidifiedPicard.isRelativeEffectiveCartierDivisor_hilbertFamily (B.inclusion.map g) _).1
    (RigidifiedPicard.isRelativeEffectiveCartierDivisor_hilbertFamily (B.inclusion.map g) _).1 h

variable {B hX g}

/-- **The Abel map** `γ_d : H ⟶ P` ([Stacks, Tag 0BA0] (4)): for `P` representing the Picard
functor and `H` representing `Hilb^d_{X/k}`, the morphism classifying the class of
`𝒪(D_univ)`. -/
def abelMap {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P)
    {d : ℕ} (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d) : H ⟶ P :=
  R.homEquiv.symm (toPicardFunctorHom B hX hk g H
    (RigidifiedPicard.familyClass (B.inclusion.map g) (hH.family (𝟙 _))))

/-- **The composite of `m : T ⟶ H` with the Abel map is the class of `𝒪(Z_m)`**, `Z_m` the
family classified by `m`. -/
theorem homEquiv_comp_abelMap {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) {d : ℕ}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d)
    {T : BigFppfOver B (Spec (.of k)) hk} (m : T ⟶ H) :
    R.homEquiv (m ≫ abelMap R hH) = toPicardFunctorHom B hX hk g T
      (RigidifiedPicard.familyClass (B.inclusion.map g)
        (hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map m))) := by
  refine (R.homEquiv_comp m _).trans ?_
  rw [abelMap, Equiv.apply_symm_apply]
  exact (toPicardFunctor_app_naturality B hX hk g m _).symm.trans
    (congrArg (toPicardFunctorHom B hX hk g T) (picardMap_familyClass B hX g hH m))

section Points

variable [IsAlgClosed k] [IsProjectiveVariety k (B.inclusion.map g)]

/-- The inverse of `Pic(X) ≃+ Pic_{X/k}(Spec k)` on the image of `Pic(X_k)`: pullback along
`X ≅ X_k`. -/
theorem ofSchemeAddEquivPicardFunctorOfCurve_symm_toPicardFunctorHom
    (c : picardAt B hX hk g (terminalTest B hk)) :
    (ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm
        (toPicardFunctorHom B hX hk g (terminalTest B hk) c) =
      Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).inv c := by
  rw [AddEquiv.symm_apply_eq]
  show toPicardFunctorHom B hX hk g (terminalTest B hk) c =
    toPicardFunctorHom B hX hk g (terminalTest B hk)
      (Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).hom
        (Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).inv c))
  rw [Stacks.Picard.schemePullbackClass_comp, Iso.hom_inv_id, Stacks.Picard.schemePullbackClass_id]

omit [IsCurve k (B.inclusion.map g)] [Smooth (B.inclusion.map g)] [IsAlgClosed k]
  [IsProjectiveVariety k (B.inclusion.map g)] in
/-- The structure morphism of the base change `X_k` along the terminal test scheme, compared
with `X ⟶ Spec k` through `X ≅ X_k`. -/
theorem baseChangeTerminal_hom_comp :
    pullback.snd (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom) ≫
        B.inclusion.map (terminalTest B hk).hom =
      (baseChangeTerminalIso B hX hk g).hom ≫ B.inclusion.map g :=
  pullback.condition.symm

omit [IsAlgClosed k] [IsProjectiveVariety k (B.inclusion.map g)] in
/-- **The class of a `k`-point of the Hilbert scheme, read on `X`.** Let `Z` be a degree-`d` family
over the terminal test scheme. Its inverse image on `X` (along `X ≅ X_k`) is an effective Cartier
divisor, finite locally free of rank `d` over `k`, whose class is the pullback of `[𝒪(Z)]`. -/
theorem exists_schemePullbackClass_familyClass {d : ℕ}
    (Z : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj (terminalTest B hk)) d) :
    ∃ (_ : Stacks.Divisors.IsEffectiveCartierDivisor
        (Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv)),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          ((Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
            B.inclusion.map g) d ∧
        Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).inv
            (RigidifiedPicard.familyClass (B.inclusion.map g) Z) =
          Stacks.Divisors.picardClass (Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv) := by
  have : IsIso (B.inclusion.map (terminalTest B hk).hom) :=
    CategoryTheory.Functor.map_isIso B.inclusion (𝟙 (B.obj hk))
  have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
        (baseChangeTerminalIso B hX hk g).inv ≫
          pullback.snd (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom)) d :=
    @Stacks.Divisors.isFiniteLocallyFreeOfRank_comap_of_isIso _ _ _
      (baseChangeTerminalIso B hX hk g).inv inferInstance _ Z.ideal d Z.isFiniteLocallyFreeOfRank
  have key : (Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
      B.inclusion.map g =
      ((Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
        (baseChangeTerminalIso B hX hk g).inv ≫
          pullback.snd (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom)) ≫
        B.inclusion.map (terminalTest B hk).hom := by
    rw [Category.assoc, Category.assoc, baseChangeTerminal_hom_comp, Iso.inv_hom_id_assoc]
  have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
        B.inclusion.map g) d := by
    rw [key]
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp_isIso _ _ d
  let : SmoothOfRelativeDimension 1 (B.inclusion.map g) :=
    smoothOfRelativeDimension_one_of_isCurve _ (B.inclusion.map g)
  have : Stacks.Morphisms.IsFiniteLocallyFree
      ((Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫ B.inclusion.map g) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d hrank
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv) :=
    (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree (B.inclusion.map g)
      (Z.ideal.comap (baseChangeTerminalIso B hX hk g).inv)).1
  exact ⟨hD, hrank, @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ _ _ _
    (RigidifiedPicard.isRelativeEffectiveCartierDivisor_hilbertFamily (B.inclusion.map g) Z).1 hD
    rfl⟩

/-- The class on `X` of `D ≫ γ_d`, for a `k`-point `D` of the Hilbert scheme, is the pullback of
the class of the family classified by `D`. -/
private theorem symm_homEquiv_comp_abelMap {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) {d : ℕ}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d) (D : terminalTest B hk ⟶ H) :
    (ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm (R.homEquiv (D ≫ abelMap R hH)) =
      Stacks.Picard.schemePullbackClass (baseChangeTerminalIso B hX hk g).inv
        (RigidifiedPicard.familyClass (B.inclusion.map g)
          (hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map D))) := by
  rw [homEquiv_comp_abelMap]
  exact ofSchemeAddEquivPicardFunctorOfCurve_symm_toPicardFunctorHom _

/-- **The Abel map has degree `d` on `k`-points**: the class of `D ≫ γ_d`, for a `k`-point `D` of
`Hilb^d_{X/k}`, is the class of an effective divisor finite locally free of rank `d` over `k`, so
has degree `d`. -/
theorem ofSchemeDegree_comp_abelMap {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) {d : ℕ}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d)
    (hdim : topologicalKrullDim X ≤ 1) (D : terminalTest B hk ⟶ H) :
    Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim
      ((ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm (R.homEquiv (D ≫ abelMap R hH))) =
        d := by
  rw [symm_homEquiv_comp_abelMap]
  obtain ⟨hD, hrank, hcl⟩ := exists_schemePullbackClass_familyClass (B := B) (hX := hX)
    (g := g) (hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map D))
  rw [hcl, Stacks.Picard.ofSchemeDegree_divisorPicardClass]
  let : Algebra k Γ(((hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map D)).ideal.comap
      (baseChangeTerminalIso B hX hk g).inv).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (((hH.family ((BigFppfOver.toOver B (Spec (.of k)) hk).map
      D)).ideal.comap (baseChangeTerminalIso B hX hk g).inv).subschemeι ≫
        B.inclusion.map g).appTop).hom.toAlgebra
  obtain ⟨-, -, h⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq _ d).1 hrank
  rw [h]

/-- **Every class of degree `d ≥ g` is the Abel map of a `k`-point of `Hilb^d_{X/k}`**: the
surjectivity of `γ_d` on `k`-points of [Stacks, Tag 0BA0] (5), read on `Pic(X)`. -/
theorem exists_comp_abelMap_eq {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) {d : ℕ}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) d)
    (hdim : topologicalKrullDim X ≤ 1) (hg : genus (B.inclusion.map g) ≤ d)
    (x : Stacks.Picard.ofScheme X)
    (hx : Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim x = d) :
    ∃ D : terminalTest B hk ⟶ H,
      (ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm (R.homEquiv (D ≫ abelMap R hH)) =
        x := by
  have : IsIso (B.inclusion.map (terminalTest B hk).hom) :=
    CategoryTheory.Functor.map_isIso B.inclusion (𝟙 (B.obj hk))
  obtain ⟨D, hD, d', hrank, hd', rfl⟩ :=
    Stacks.Picard.exists_eq_picardClass_of_genus_le_ofSchemeDegree k (B.inclusion.map g) hdim x
      (by rw [hx]; exact_mod_cast hg)
  have hdd : d' = d := by exact_mod_cast hd'.trans hx
  subst hdd
  have := hrank
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (D.subschemeι ≫ B.inclusion.map g ≫ inv (B.inclusion.map (terminalTest B hk).hom)) d' := by
    rw [← Category.assoc]
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp_isIso _ _ d'
  have hq : pullback.snd (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom) =
      (baseChangeTerminalIso B hX hk g).hom ≫ B.inclusion.map g ≫
        inv (B.inclusion.map (terminalTest B hk).hom) := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact baseChangeTerminal_hom_comp
  have hZ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((D.comap (baseChangeTerminalIso B hX hk g).hom).subschemeι ≫
        pullback.snd (B.inclusion.map g) (B.inclusion.map (terminalTest B hk).hom)) d' := by
    rw [hq]
    exact Stacks.Divisors.isFiniteLocallyFreeOfRank_comap_of_isIso _ _ D d'
  let Z : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj (terminalTest B hk)) d' :=
    ⟨D.comap (baseChangeTerminalIso B hX hk g).hom, hZ⟩
  refine ⟨(fullyFaithfulToOver B hk).preimage (hH.family.symm Z), ?_⟩
  rw [symm_homEquiv_comp_abelMap, Functor.FullyFaithful.map_preimage, Equiv.apply_symm_apply]
  obtain ⟨hD', -, hcl⟩ := exists_schemePullbackClass_familyClass (B := B) (hX := hX)
    (g := g) Z
  rw [hcl]
  have h : (D.comap (baseChangeTerminalIso B hX hk g).hom).comap
      (baseChangeTerminalIso B hX hk g).inv = D := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  exact @Stacks.Divisors.picardClass_congr _ _ _ h hD' hD

end Points

end Stacks.PicardFunctor

end
