module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingAffineSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPointSpaceMap
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# The étale local chart of a quasi-DM stack with separated diagonal

The proofs of **Stacks 0DU3**, **Stacks 0DU4** and **Stacks 0DU5** share their first part. Let
`𝒳` be an algebraic stack which is quasi-DM with separated diagonal, and let `x ∈ |𝒳|`. Choose
an affine scheme `U` and a flat, locally finitely presented, locally quasi-finite morphism
`U ⟶ 𝒳` whose image contains `x` (Stacks 06MF), let `R = U ×_𝒳 U` (Stacks 04T4, a scheme by
Stacks 03XX), and replace `𝒳` by the open substack which is the image of `U` (Stacks 04XL,
06FJ), so that `𝒳 = [U/R]` (Stacks 04WY). Then for an étale neighbourhood `U' ⟶ U` and an open
subgroupoid `P` of `R|_{U'}`, the quotient stack `[U'/P]` maps to `𝒳` by a 1-morphism which is
representable by algebraic spaces and étale (Stacks 0DU2), and the automorphism groups and self
products of the points of `[U'/P]` are computed by `P` inside `R|_{U'}`.

This file states that shared part as one proposition,
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem`, and proves
**Stacks 0DU4** from it. No declaration here carries a `@[stacks]` attribute. The
proposition is not a tag of the Stacks project; it is the common first part of three proofs,
and `exists_etale_affineGroupoid_neighborhood_preserving_automorphisms_of_localStructure`
records exactly what Stacks 0DU4 still needs of it.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleLocalStructure.IsFiniteOverBase`: the property "finite" of an
  algebraic space over an object of the site, the instance of Remark 0DTU that Stacks 0DU4
  uses.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureAt`: the chart groupoid at a point
  together with the properties of the quotient stacks of its étale-local open subgroupoids.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem`: that chart exists at every
  point of every quasi-DM algebraic stack with separated diagonal.

## Main results

* `exists_etale_affineGroupoid_neighborhood_preserving_automorphisms_of_localStructure`
  (in `AlgebraicGeometry.Stack.EtaleLocalStructure`): **Stacks 0DU4** from the chart.
  Stacks 0DTE, in the form
  `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isFinite_flat_splitting`, provides the
  splitting.

## References

* [Stacks Project, Tag 0DTE](https://stacks.math.columbia.edu/tag/0DTE)
* [Stacks Project, Tag 0DTU](https://stacks.math.columbia.edu/tag/0DTU)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The property "finite" of an algebraic space over an object of the site.** An algebraic
space `G` over `U` is finite when its structure morphism `G ⟶ U` is a finite morphism of
algebraic spaces (Stacks 03ZP). Read at the automorphism group algebraic space of a point, this
is the phrase "the automorphism group is finite" of Remark 0DTU. -/
abbrev IsFiniteOverBase (U : BigFppfOver B S hS)
    (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) : Prop :=
  Space.IsFinite B U.left.1 U.left.2 ((isTerminal_siteTerminalSpace B S hS U).from G)

/-- **The étale local chart of a quasi-DM stack with separated diagonal at a point `x`.**

* A groupoid scheme `G = (U, R, s, t, c)` over `S` with `U` affine and with `s` and `t`
  separated, flat and locally of finite presentation and `s` locally quasi-finite, a point
  `u ∈ U`, and the containments in the site that its realization needs. In the proofs this is
  `R = U ×_𝒳 U` for a flat, locally finitely presented, locally quasi-finite chart `U ⟶ 𝒳`
  through `x`.
* If the automorphism group of `𝒳` at `x` is finite, only finitely many stabilizer points of
  `G` lie over `u`. If `x` is represented by a quasi-compact morphism from the spectrum of a
  field, the fibre `u ×_{U, t} R` is quasi-compact.
* For every morphism `ψ : K ⟶ G` of groupoid schemes which is étale on objects and fully
  faithful on generalized points (a restriction of `G` to an étale neighbourhood, possibly taken
  in two steps), with `K`'s source and target flat and locally of finite presentation, for every
  point `u'` of `K` over `u`, and for every open subgroupoid `φ : H ⟶ K` on the same objects
  whose realization exists: an algebraic stack `𝒰` equivalent to `[U'/H]`, quasi-DM, with a
  1-morphism `f : 𝒰 ⟶ 𝒳` which is representable by algebraic spaces and étale, and a point
  `v ∈ |𝒰|` over `x`. If `H` contains every stabilizer point of `K` over `u'`, then `f`
  induces an isomorphism of automorphism groups at `v`. If `H` contains every arrow of `K` with
  source and target `u'`, then `f` induces an equivalence of self products at `v`, the
  hypothesis of Stacks 0DTI. -/
def LocalStructureAt (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳) :
    Prop :=
  ∃ (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (_hU : B.Contains G.objects.left) (_hR : B.Contains G.arrows.left)
    (_hP : B.Contains (pullback G.source G.target).left)
    (_hK : B.Contains (Spec (G.objects.left.residueField u))),
    IsAffine G.objects.left ∧
    AlgebraicGeometry.IsSeparated G.source.left ∧ AlgebraicGeometry.IsSeparated G.target.left ∧
    Flat G.source.left ∧ LocallyOfFinitePresentation G.source.left ∧
    Flat G.target.left ∧ LocallyOfFinitePresentation G.target.left ∧
    LocallyQuasiFinite G.source.left ∧
    (AutomorphismGroupHasProperty B S hS (IsFiniteOverBase B S hS) x →
      Set.Finite {g : (AlgebraicGeometry.stabilizer G).left |
        (AlgebraicGeometry.stabilizer G).hom g = u}) ∧
    ((∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
          IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) →
      CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.target.left)) ∧
    ∀ (K : Stacks.Groupoids.GroupoidScheme S) (ψ : Stacks.Groupoids.GroupoidScheme.Hom K G)
      (u' : K.objects.left), Etale ψ.mapObjects.left →
      (∀ T : Over S, Nonempty (ψ.evaluation T).FullyFaithful) →
      ψ.mapObjects.left.base u' = u →
      Flat K.source.left → LocallyOfFinitePresentation K.source.left →
      Flat K.target.left → LocallyOfFinitePresentation K.target.left →
      ∀ (H : Stacks.Groupoids.GroupoidScheme S) (φ : Stacks.Groupoids.GroupoidScheme.Hom H K),
        (∃ hobj : H.objects = K.objects, φ.mapObjects = eqToHom hobj) →
        AlgebraicGeometry.IsOpenImmersion φ.mapArrows.left →
        ∀ (hHU : B.Contains H.objects.left) (hHR : B.Contains H.arrows.left)
          (hHP : B.Contains (pullback H.source H.target).left),
        ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (f : 𝒰 ⟶ 𝒳)
          (v : AlgebraicStacks.points B S hS 𝒰),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (quotientStack (H.realization B hS hHU hHR hHP)).p 𝒰.val.val.p) ∧
          AlgebraicStacks.pointsMap B S hS f v = x ∧
          IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
          IsEtale B S hS f ∧
          AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒰 ∧
          ((∀ y : (AlgebraicGeometry.stabilizer K).left,
              (AlgebraicGeometry.stabilizer K).hom.base y = u' →
                ∃ p : H.arrows.left,
                  φ.mapArrows.left.base p = (AlgebraicGeometry.stabilizerArrow K).base y) →
            InducesIsomorphismAt B S hS f v) ∧
          ((∀ r : K.arrows.left, K.source.left.base r = u' → K.target.left.base r = u' →
              ∃ p : H.arrows.left, φ.mapArrows.left.base p = r) →
            HasSelfProductEquivalenceAt B S hS f v)

/-- **The étale local chart exists**:
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureAt` holds at every point of every
algebraic stack which is quasi-DM with separated diagonal. -/
def LocalStructureTheorem : Prop :=
  ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS), AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳 →
    AlgebraicStacks.IsSeparated B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)) →
    ∀ x : AlgebraicStacks.points B S hS 𝒳, LocalStructureAt B S hS hZ 𝒳 x

/-- **Stacks 0DU4 from the étale local chart.** Let `𝒳` be an algebraic stack which is quasi-DM
with separated diagonal, and let `x ∈ |𝒳|` be a point at which the automorphism group of `𝒳` is
finite (Remark 0DTU). Granting the étale local chart
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem`, there is a 1-morphism
`f : 𝒰 ⟶ 𝒳` of algebraic stacks with
1. a point `v ∈ |𝒰|` mapping to `x` at which `f` induces an isomorphism between automorphism
   groups (Stacks 0DTW),
2. `f` representable by algebraic spaces and étale,
3. `𝒰 = [U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and `s` and `t`
   finite, flat and locally of finite presentation.

This is the source's proof. The chart supplies the groupoid `G = U ×_𝒳 U` with finitely many
stabilizer points over `u` (the automorphism group at `x` being finite), Stacks 0DTE supplies
an affine elementary étale neighbourhood `(U'', u'')` over which the restriction of `G` is split,
the splitting `P` is a groupoid of the shape of clause (3), and the chart's quotient stack
`[U''/P]` maps étale and representably to `𝒳`. Since `P` contains the stabilizer over `u''`,
that 1-morphism preserves automorphism groups at the image of `u''`. -/
theorem exists_etale_affineGroupoid_neighborhood_preserving_automorphisms_of_localStructure
    (hLS : LocalStructureTheorem.{u, w} B S hS hZ)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hDM : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (hSep : AlgebraicStacks.IsSeparated B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hAut : AutomorphismGroupHasProperty B S hS (IsFiniteOverBase B S hS) x) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (f : 𝒰 ⟶ 𝒳) (v : AlgebraicStacks.points B S hS 𝒰)
      (G : Stacks.Groupoids.GroupoidScheme S) (hU : B.Contains G.objects.left)
      (hR : B.Contains G.arrows.left) (hP : B.Contains (pullback G.source G.target).left),
      AlgebraicStacks.pointsMap B S hS f v = x ∧
      InducesIsomorphismAt B S hS f v ∧
      IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
      IsEtale B S hS f ∧
      IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
      AlgebraicGeometry.IsFinite G.source.left ∧ AlgebraicGeometry.IsFinite G.target.left ∧
      Flat G.source.left ∧ Flat G.target.left ∧
      LocallyOfFinitePresentation G.source.left ∧ LocallyOfFinitePresentation G.target.left ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) := by
  obtain ⟨G, u, hU, hR, hP, hK, _, _, _, _, _, _, _, _, hfinImp, -, hiii⟩ :=
    hLS 𝒳 hDM hSep x
  obtain ⟨U'', g, u'', _, _, hbase, -, hall⟩ :=
    Stacks.Groupoids.GroupoidScheme.exists_isAffine_isFinite_flat_splitting G u B hS hU hR hP hK
      (hfinImp hAut)
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  obtain ⟨hRsf, hRsl, hRtf, hRtl, H, φ, hobj, hopen, hstab, hHo, hHa, hHsfin, hHsf, hHsl,
    hHtfin, hHtf, hHtl⟩ := hall R
  have hHU : B.Contains H.objects.left := by
    obtain ⟨hobj', -⟩ := hobj
    rw [hobj', R.objects_eq]
    exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g.left hU
  have hHR : B.Contains H.arrows.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact H.source.left hHU
  have hHP : B.Contains (pullback H.source H.target).left :=
    BigFppfSite.contains_pullback_left B H.source H.target hHR hHR
  have hRet : Etale R.hom.mapObjects.left := by
    rw [R.mapObjects_eq, Over.comp_left]
    have : IsIso (eqToHom R.objects_eq).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (eqToHom R.objects_eq)))
    infer_instance
  have hRbase : R.hom.mapObjects.left.base ((eqToHom R.objects_eq.symm).left.base u'') = u := by
    rw [R.mapObjects_eq, Over.comp_left, Scheme.Hom.comp_apply,
      Stacks.Groupoids.GroupoidScheme.over_eqToHom_apply_symm, hbase]
  obtain ⟨𝒰, f, v, he, hpts, hrep, hét, -, hiv, -⟩ :=
    hiii R.groupoid R.hom ((eqToHom R.objects_eq.symm).left.base u'') hRet
      R.evaluation_fullyFaithful hRbase hRsf hRsl hRtf hRtl H φ hobj hopen hHU hHR hHP
  exact ⟨𝒰, f, v, H, hHU, hHR, hHP, hpts, hiv hstab, hrep, hét, hHo, hHa, hHsfin, hHtfin,
    hHsf, hHtf, hHsl, hHtl, he⟩

/-- **A finite algebraic space over a finite affine base which is a scheme has finitely many
points.** Let `U` be an object of the site whose underlying scheme is affine with finitely many
points (for instance the spectrum of a field), and let `G` be an algebraic space over `U`
represented by an object `V` of the site of `U`. If `G` is finite over `U`
(`AlgebraicGeometry.Stack.EtaleLocalStructure.IsFiniteOverBase`), then `V` has finitely many
points. This is how the finiteness of an automorphism group in the sense of Remark 0DTU is read
off a scheme representing it. -/
theorem finite_of_isFiniteOverBase_of_iso (U : BigFppfOver B S hS)
    [IsAffine U.left.1] [Finite U.left.1]
    (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) (V : BigFppfOver B U.left.1 U.left.2)
    (eV : G ≅ yoneda.obj V) (hG : IsFiniteOverBase B S hS U G) :
    Finite V.left.1 := by
  let U' : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  have hU' : IsAffine ((BigFppfOver.toScheme B U.left.1 U.left.2).obj U') :=
    inferInstanceAs (IsAffine U.left.1)
  let ξ : yoneda.obj U' ⟶ siteTerminalSpace B S hS U := yoneda.map (terminal.from U')
  have : IsIso ξ := by
    have : IsIso (terminal.from U') :=
      isIso_of_isTerminal Over.mkIdTerminal terminalIsTerminal _
    infer_instance
  obtain ⟨V', q, i, hV'aff, hfin, hpb⟩ := hG U' hU' ξ
  have : IsIso i := hpb.isIso_fst_of_isIso
  let eYo : yoneda.obj V' ≅ yoneda.obj V := asIso i ≪≫ eV
  let eVV : V' ≅ V := Yoneda.fullyFaithful.preimageIso eYo
  have := hfin
  have : Finite ((BigFppfOver.toScheme B U.left.1 U.left.2).obj V') := by
    have h := ((BigFppfOver.toScheme B U.left.1 U.left.2).map q).finite_preimage
      (Set.finite_univ : (Set.univ : Set U.left.1).Finite)
    rw [Set.preimage_univ] at h
    exact Set.finite_univ_iff.mp h
  exact Finite.of_equiv _
    ((BigFppfOver.toScheme B U.left.1 U.left.2).mapIso eVV).hom.homeomorph.toEquiv

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
