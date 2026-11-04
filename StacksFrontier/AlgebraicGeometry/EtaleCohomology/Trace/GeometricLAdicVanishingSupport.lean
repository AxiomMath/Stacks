module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingAbsolute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.DenseOpen

/-!
# Vanishing above twice the dimension of an open subscheme carrying the sheaf

Let `Y` be proper over a separably closed field `K`, let `o : U ⟶ Y` be a quasi-compact open
immersion, and let `G` be a torsion abelian sheaf on `Y_étale` whose restriction to every open
subscheme disjoint from `o(U)` vanishes. Then `Hᵠ(Y, G) = 0` for `q > 2 dim U`, granted the
absolute case of [Stacks, Tag 095U] (`ProperSeparablyClosedSheafHVanishingStatement`).

This is how the vanishing of `Hⁱ_c(X_k̄, -)` above `2 dim X` in [Stacks, Tag 03V2] comes out of
Tag 095U: `Hⁱ_c` is computed on the base change `X̄_k̄` of a compactification, whose dimension may
exceed that of `X`, of a sheaf extended by zero from `X_k̄`.

The sheaf is supported on the scheme-theoretic closure `i : Z ⟶ Y` of `U`, so the sequence
`0 → v_! v⁻¹G → G → i_* i⁻¹G → 0` of [Stacks, Tag 095L] for the open complement `v` of `Z`
identifies `G` with `i_* i⁻¹G`; as `i` is finite, `Hᵠ(Y, i_* -) = Hᵠ(Z, -)`. Finally `Z` is
proper over `K` and has `U` as a dense open, so `dim Z ≤ dim U`
(`AlgebraicGeometry.topologicalKrullDim_le_of_isOpen_of_dense`), and Tag 095U applies on `Z`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_inverseImage`: the
  cohomology of a sheaf supported on a closed subscheme is that of its restriction there.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint`: the
  vanishing above `2 dim U`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isZero_etaleRestriction_of_isEmpty`: the case of
  an empty `U`, in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomology of a sheaf supported on a closed subscheme.** Let `i : Z ⟶ Y` be a closed
immersion with open complement `v : V ⟶ Y`, and `G` an abelian sheaf on `Y_étale` whose
restriction to `V` is zero. Then `Hᵠ(Y, G) = 0` as soon as `Hᵠ(Z, i⁻¹G) = 0`: the sequence
`0 → v_! v⁻¹G → G → i_* i⁻¹G → 0` ([Stacks, Tag 095L]) identifies `G` with `i_* i⁻¹G`, and `i_*`
is exact and preserves injectives, so `Hᵠ(Y, i_* -) = Hᵠ(Z, -)`. -/
theorem subsingleton_sheafH_of_isZero_etaleRestriction_of_inverseImage {Z V Y : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (v : V ⟶ Y) [IsOpenImmersion v]
    (hiv : Set.range v = (Set.range i)ᶜ) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsZero ((etaleRestriction.{u, 0} v).obj G)) (q : ℕ)
    (hZ : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i).obj G) q)) :
    Subsingleton (Sheaf.H.{u + 1} G q) := by
  obtain ⟨hw, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i v hiv G
  have : (extensionByZero.{u, 0} v).Additive := (extensionByZeroAdj.{u, 0} v).left_adjoint_additive
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G) :=
    hS.exact.mono_g (((extensionByZero.{u, 0} v).map_isZero hG).eq_of_src _ _)
  have : Epi ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G) := hS.epi_g
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G) :=
    isIso_of_mono_of_epi _
  have : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    Stacks.Cohomology.GlobalSections.additive_Γ.{0, u, u + 1} _
  have : (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).Additive :=
    Stacks.Cohomology.GlobalSections.additive_Γ.{0, u, u + 1} _
  have : (etaleAbelianDirectImage.{u, 0} i).PreservesHomology :=
    etaleAbelianDirectImage_preservesHomology_of_isIntegralHom.{u, 0} i
  have : PreservesFiniteLimits (etaleAbelianDirectImage.{u, 0} i) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, 0} i) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have : (etaleAbelianDirectImage.{u, 0} i).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} i)
  have hac : ∀ I : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}, Injective I →
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightAcyclic
        ((etaleAbelianDirectImage.{u, 0} i).obj I) := fun I _ ↦
    Stacks.RightAcyclicProduct.rightAcyclic_of_injective _ _
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
    at hZ ⊢
  refine IsZero.of_iso ?_ (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
    q).mapIso (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app G)))
  exact hZ.of_iso (((Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
    (etaleAbelianDirectImage.{u, 0} i) (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    hac q).app _).symm ≪≫ (Functor.rightDerivedIsoOfNatIso
      (etaleAbelianDirectImageCompΓIso.{u, 0} i) q).app _)

/-- If a sheaf restricts to zero on every open disjoint from `o(U)`, its cohomology vanishes as
soon as that of its restriction to the scheme-theoretic closure of `U` does. -/
private theorem subsingleton_sheafH_of_isZero_etaleRestriction_of_imageι {Y U : Scheme.{u}}
    (o : U ⟶ Y) [IsOpenImmersion o] [QuasiCompact o]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hV : ∀ {V : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v],
      Disjoint (Set.range v) (Set.range o) → IsZero ((etaleRestriction.{u, 0} v).obj G))
    (q : ℕ)
    (hZ : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} o.imageι).obj G) q)) :
    Subsingleton (Sheaf.H.{u + 1} G q) := by
  let Vo : Y.Opens :=
    ⟨(Set.range o.imageι)ᶜ, isOpen_compl_iff.2 o.imageι.isClosedEmbedding.isClosed_range⟩
  have hrange : Set.range Vo.ι = (Set.range o.imageι)ᶜ := Scheme.Opens.range_ι Vo
  refine subsingleton_sheafH_of_isZero_etaleRestriction_of_inverseImage o.imageι Vo.ι hrange G
    (hV Vo.ι ?_) q hZ
  rw [hrange, Set.disjoint_compl_left_iff_subset]
  exact subset_closure.trans (Scheme.Hom.range_imageι o).ge

/-- **Vanishing above twice the dimension of an open carrying the sheaf.** Let `Y` be proper
over a separably closed field, `o : U ⟶ Y` a quasi-compact open immersion with `dim U ≤ n`, and
`G` a torsion abelian sheaf on `Y_étale` whose restriction to every open subscheme disjoint from
`o(U)` is zero. Then `Hᵠ(Y, G) = 0` for `q > 2n`, granted the absolute case of
[Stacks, Tag 095U]: `G` is supported on the scheme-theoretic closure `Z` of `U`, which is proper
over the field and has `U` as a dense open, so `dim Z ≤ dim U`. -/
theorem subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint
    (h095U : ProperSeparablyClosedSheafHVanishingStatement.{u}) (K : Type u) [Field K]
    [IsSepClosed K] {Y U : Scheme.{u}} (g : Y ⟶ Spec (.of K)) [IsProper g] (o : U ⟶ Y)
    [IsOpenImmersion o] [QuasiCompact o] (n : ℕ) (hU : topologicalKrullDim U ≤ n)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology G)
    (hV : ∀ {V : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v],
      Disjoint (Set.range v) (Set.range o) → IsZero ((etaleRestriction.{u, 0} v).obj G))
    (q : ℕ) (hq : 2 * n < q) :
    Subsingleton (Sheaf.H.{u + 1} G q) := by
  let b := o.imageι
  refine subsingleton_sheafH_of_isZero_etaleRestriction_of_imageι o G hV q ?_
  have : IsProper (b ≫ g) := inferInstance
  have : IsLocallyNoetherian o.image :=
    LocallyOfFiniteType.isLocallyNoetherian (b ≫ g)
  have : CompactSpace o.image := QuasiCompact.compactSpace_of_compactSpace (b ≫ g)
  have : AlgebraicGeometry.IsNoetherian o.image := ⟨⟩
  have hdim : topologicalKrullDim o.image ≤ n := by
    refine (topologicalKrullDim_le_of_isOpen_of_dense K o.image (b ≫ g)
      (Set.range o.toImage) o.toImage.isOpenEmbedding.isOpen_range
      o.toImage.denseRange).trans ?_
    rwa [← IsHomeomorph.topologicalKrullDim_eq _
      (o.toImage.isOpenEmbedding.isEmbedding.toHomeomorph).isHomeomorph]
  exact h095U K (b ≫ g) n hdim _
    (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} b G hG) q hq

/-- **A sheaf vanishing away from an empty open has no cohomology.** If `o : U ⟶ Y` is a
quasi-compact open immersion from an empty scheme and the abelian sheaf `G` restricts to zero on
every open subscheme disjoint from `o(U)`, then `Hᵠ(Y, G) = 0` in every degree: `G` is supported
on the scheme-theoretic closure of `U`, which is empty. -/
theorem subsingleton_sheafH_of_isZero_etaleRestriction_of_isEmpty {Y U : Scheme.{u}}
    (o : U ⟶ Y) [IsOpenImmersion o] [QuasiCompact o] [IsEmpty U]
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hV : ∀ {V : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v],
      Disjoint (Set.range v) (Set.range o) → IsZero ((etaleRestriction.{u, 0} v).obj G))
    (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} G q) := by
  let : ∀ S : Scheme.{u},
      HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun S ↦
      have := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} S
      IsGrothendieckAbelian.hasExt.{u + 1} _
  refine subsingleton_sheafH_of_isZero_etaleRestriction_of_imageι o G hV q ?_
  have : IsEmpty o.image := by
    refine ⟨fun z ↦ ?_⟩
    have hz : o.imageι z ∈ closure (Set.range o) := by
      rw [← Scheme.Hom.range_imageι]
      exact ⟨z, rfl⟩
    rwa [Set.range_eq_empty o, closure_empty] at hz
  exact subsingleton_sheafH_of_isEmpty_sheafUniverse.{u, 0} _ q

end Stacks.EtaleCohomology

end
