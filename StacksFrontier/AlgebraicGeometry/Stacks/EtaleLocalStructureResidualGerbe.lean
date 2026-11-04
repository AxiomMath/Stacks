module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingOfCompactFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChart

/-!
# An étale neighbourhood preserving the residual gerbe (Stacks 0DU5, from the étale local chart)

**Stacks 0DU5.** Let `𝒳` be an algebraic stack which is quasi-DM with separated diagonal, and let
`x ∈ |𝒳|` be a point which can be represented by a quasi-compact morphism `Spec k ⟶ 𝒳`. Then there
is a 1-morphism of algebraic stacks `g : 𝒰 ⟶ 𝒳` with

1. a point `u ∈ |𝒰|` mapping to `x` such that `g` induces an isomorphism between the residual
   gerbes at `u` and `x`,
2. `𝒰 ⟶ 𝒳` representable by algebraic spaces and étale,
3. `𝒰 = [U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and `s`, `t`
   finite, flat and locally of finite presentation.

This file runs the source's proof from two inputs that are stated as explicit hypotheses and
proved elsewhere: the étale local chart shared by Stacks 0DU3, 0DU4 and 0DU5,
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem` (the first part of the proof
of Stacks 0DU3 together with Stacks 0DU2), and the existence of residual gerbes on quasi-DM
algebraic stacks (Stacks 06UI). The theorem is therefore not registered.

## The argument

The chart gives a groupoid scheme `G = (U, R, s, t, c)` with `U` affine and `s`, `t` flat, locally
of finite presentation, separated and (with `s`) locally quasi-finite, and a point `u ∈ U` over
`x`. Because `x` has a quasi-compact representative, the fibre `u ×_{U, t} R` is quasi-compact,
which is the source's "`F` is quasi-compact" (Stacks 0DTK). It follows that the set of arrows with
source and target `u` is finite (the special case of Stacks 06S0 used by the source), so the
assumptions of Stacks 04RZ hold, and after an affine elementary étale neighbourhood
`(U'', u'') ⟶ (U, u)` the restriction `R|_{U''}` has a strong splitting `P` over `u''`, which is a
groupoid scheme with affine structure schemes and finite, flat, locally finitely presented source
and target
(`AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre`).

The chart then supplies `𝒰 = [U''/P]` with its étale representable 1-morphism to `𝒳` and a point
`v` over `x`, and, since `P` contains every arrow of `R|_{U''}` with source and target `u''`, the
self 2-fibre product comparison `u'' ×_𝒰 u'' ⟶ u'' ×_𝒳 u''` is an equivalence. The residual
gerbes at `v` and `x` exist by Stacks 06UI, `𝒰` being quasi-DM, and **Stacks 0DTI** turns the
equivalence of self products into the isomorphism of residual gerbes.

## Main results

* `EtaleLocalStructure.exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure`:
  Stacks 0DU5 from the étale local chart and the existence of residual gerbes on quasi-DM stacks.

## References

* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 06S0](https://stacks.math.columbia.edu/tag/06S0)
* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The target of a groupoid scheme is locally quasi-finite when its source is: the target is the
inverse followed by the source, and the inverse is an isomorphism. -/
theorem locallyQuasiFinite_target_of_source (G : Stacks.Groupoids.GroupoidScheme S)
    [LocallyQuasiFinite G.source.left] : LocallyQuasiFinite G.target.left := by
  have := groupoidInverse_left_isIso G
  rw [show G.target.left = G.inverse.left ≫ G.source.left by
    rw [← Over.comp_left, G.source_inverse]]
  infer_instance

/-- **Stacks 0DU5 from the étale local chart.** Let `𝒳` be an algebraic stack which is quasi-DM
with separated diagonal, and let `x ∈ |𝒳|` be represented by a quasi-compact morphism from the
spectrum of a field. Granting the étale local chart
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem` and the existence of residual
gerbes at every point of a quasi-DM algebraic stack (Stacks 06UI), there is a 1-morphism
`f : 𝒰 ⟶ 𝒳` of algebraic stacks with

1. a point `v ∈ |𝒰|` mapping to `x`, the residual gerbes of `𝒰` at `v` and of `𝒳` at `x`
   existing, and the 1-morphism between them induced by `f` (Stacks 0DTH) being an isomorphism
   for every choice of them;
2. `f` representable by algebraic spaces and étale;
3. `𝒰` equivalent to `[U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and
   `s` and `t` finite, flat and locally of finite presentation.

See the module docstring for the proof. -/
theorem exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure
    (hLS : LocalStructureTheorem.{u, w} B S hS hZ)
    (hRG : ∀ (𝒴 : AlgebraicStacks.{u, w} B S hS), AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒴 →
      ∀ y : AlgebraicStacks.points B S hS 𝒴,
        ∃ Q : ObjectProperty 𝒴.val.val.obj, IsResidualGerbeAt B S hS 𝒴 y Q)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hDM : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (hSep : AlgebraicStacks.IsSeparated B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (f : 𝒰 ⟶ 𝒳) (v : AlgebraicStacks.points B S hS 𝒰)
      (G : Stacks.Groupoids.GroupoidScheme S) (hU : B.Contains G.objects.left)
      (hR : B.Contains G.arrows.left) (hP : B.Contains (pullback G.source G.target).left),
      AlgebraicStacks.pointsMap B S hS f v = x ∧
      (∃ P : ObjectProperty 𝒰.val.val.obj, IsResidualGerbeAt B S hS 𝒰 v P) ∧
      (∃ Q : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x Q) ∧
      (∀ (P : ObjectProperty 𝒰.val.val.obj) (Q : ObjectProperty 𝒳.val.val.obj)
        (hv : IsResidualGerbeAt B S hS 𝒰 v P)
        (hx : IsResidualGerbeAt B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS f v) Q),
        Nonempty (Functor.IsEquivalenceOver
          (fullSubcategoryAlgebraicStack 𝒰 P hv.2.choose).val.val.p
          (fullSubcategoryAlgebraicStack 𝒳 Q hx.2.choose).val.val.p
          (CatFiberedInGroupoids.homFunctor
            (residualGerbeMap B S hS f hv.2.choose hx.2.choose
              (map_mem_of_isResidualGerbeAt B S hS f v _ rfl hv hx)).hom))) ∧
      IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
      IsEtale B S hS f ∧
      IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
      AlgebraicGeometry.IsFinite G.source.left ∧ AlgebraicGeometry.IsFinite G.target.left ∧
      Flat G.source.left ∧ Flat G.target.left ∧
      LocallyOfFinitePresentation G.source.left ∧ LocallyOfFinitePresentation G.target.left ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) := by
  obtain ⟨G, u, hU, hR, hP, hK, haff, hss, hts, hsf, hsl, htf, htl, hlqf, -, hcpt, hiii⟩ :=
    hLS 𝒳 hDM hSep x
  have := haff
  have := hss
  have := hts
  have := hsf
  have := hsl
  have := htf
  have := htl
  have := hlqf
  have := locallyQuasiFinite_target_of_source S G
  have := hcpt hqc
  obtain ⟨U'', g, u'', haffU, het, hbase, -, hall⟩ :=
    AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre G u B hS
      hU hR hP hK
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  obtain ⟨⟨hRsf, hRsl, hRtf, hRtl⟩, Psplit, hHo, hHa, hHsfin, hHsf, hHsl, hHtfin, hHtf, hHtl⟩ :=
    hall R
  have := haffU
  have := het
  have := hHsfin
  have hHU : B.Contains Psplit.subgroupoid.objects.left := by
    rw [Psplit.objects_eq, R.objects_eq]
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g.left hU
  have hHR : B.Contains Psplit.subgroupoid.arrows.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact Psplit.subgroupoid.source.left hHU
  have hHP : B.Contains
      (pullback Psplit.subgroupoid.source Psplit.subgroupoid.target).left :=
    BigFppfSite.contains_pullback_left B Psplit.subgroupoid.source Psplit.subgroupoid.target
      hHR hHR
  have hRet : Etale R.hom.mapObjects.left := by
    rw [R.mapObjects_eq, Over.comp_left]
    have : IsIso (eqToHom R.objects_eq).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq)))
    infer_instance
  have hRbase : R.hom.mapObjects.left.base ((eqToHom R.objects_eq.symm).left.base u'') = u := by
    rw [R.mapObjects_eq, Over.comp_left, Scheme.Hom.comp_apply,
      Stacks.Groupoids.GroupoidScheme.over_eqToHom_apply_symm, hbase]
  obtain ⟨𝒰, f, v, he, hpts, hrep, hét, hqDM, -, hself⟩ :=
    hiii R.groupoid R.hom ((eqToHom R.objects_eq.symm).left.base u'') hRet
      R.evaluation_fullyFaithful hRbase hRsf hRsl hRtf hRtl Psplit.subgroupoid Psplit.inclusion
      ⟨Psplit.objects_eq, Psplit.mapObjects_eq⟩ Psplit.arrows_open hHU hHR hHP
  refine ⟨𝒰, f, v, Psplit.subgroupoid, hHU, hHR, hHP, hpts, hRG 𝒰 hqDM v, hRG 𝒳 hDM x,
    fun P Q hv hx ↦
      isEquivalenceOver_residualGerbeMap_of_hasSelfProductEquivalenceAt B S hS f v P Q hv hx
        (hself fun r h₁ h₂ ↦ Psplit.contains_stabilizer r h₁ h₂),
    hrep, hét, hHo, hHa, hHsfin, hHtfin, hHsf, hHtf, hHsl, hHtl, he⟩

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
