module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import all StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Additions to `UnramifiedEtaleDescent`

Declarations supplementing the module above, kept in their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

add_to_stacks 04CY "fibre products in the big affine fppf site"
  AlgebraicGeometry.hasPullbacks_bigAffineFppf

add_to_stacks 04CY "preservation by the big affine fppf functor to schemes"
  AlgebraicGeometry.preservesPullbacks_bigAffineFppfToScheme

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale covering family of local lifts.** In a representable, surjective, étale
situation with formally smooth composite, a lifting problem for the second transformation along
a square-zero closed immersion with affine target is solved over an étale covering family of
affine objects: the affine étale neighbourhoods of
`AlgebraicGeometry.Space.exists_etale_affine_local_lift` are jointly surjective, the immersion
being a thickening, so the family generates a covering sieve for the étale topology on the
slice.

This is the étale-local existence of lifts, the half of the descent of formal smoothness along
a surjective étale chart which does not need the sheaf of lifts to be a trivial torsor. What it
does not give is a section over the thickening itself: for that the local sections have to agree
on pairwise fibre products, which for a formally étale composite is uniqueness
(`AlgebraicGeometry.Space.formallyEtale_of_comp`) and for a formally smooth one is the
triviality of the pseudo-torsor of lifts. -/
public theorem exists_etale_cover_local_lifts
    (s : RepresentableSurjectiveEtaleSituation.{u})
    (T T' : BigFppfOver s.B s.S s.hS) (i : T ⟶ T')
    (hT' : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj T'))
    (hi : IsSquareZeroClosedImmersion s.B s.S s.hS i)
    (x : s.G.obj (op T)) (y : s.H.obj (op T'))
    (hxy : s.b.app (op T) x = s.H.map i.op y)
    (hsmooth : FormallySmooth (s.a ≫ s.b)) :
    ∃ (ι : Type u) (U : ι → BigFppfOver s.B s.S s.hS) (j : ∀ k, U k ⟶ T')
      (z : ∀ k, s.G.obj (op (U k))),
      (∀ k, IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj (U k))) ∧
      Sieve.ofArrows (fun k : ULift.{u + 1} ι ↦ U k.down) (fun k ↦ j k.down) ∈
        ((etaleTopology s.B).over (s.B.obj s.hS)) T' ∧
      (∀ k, s.b.app (op (U k)) (z k) = s.H.map (j k).op y) ∧
      ∀ (k) (V : BigFppfOver s.B s.S s.hS) (f : V ⟶ T) (g : V ⟶ U k),
        f ≫ i = g ≫ j k → s.G.map f.op x = s.G.map g.op (z k) := by
  classical
  have hiSurj : Function.Surjective ((BigFppfOver.toScheme s.B s.S s.hS).map i).base :=
    (Stacks.Thickenings.IsFirstOrderThickening.isThickening
      (i := (BigFppfOver.toScheme s.B s.S s.hS).map i) hi).2
  choose U j z hUaff hjet hjhit hjb hcompat using
    fun t : (BigFppfOver.toScheme s.B s.S s.hS).obj T ↦
      exists_etale_affine_local_lift s T T' i hT' hi x y hxy hsmooth t
  refine ⟨↥((BigFppfOver.toScheme s.B s.S s.hS).obj T), U, j, z, hUaff, ?_, hjb, hcompat⟩
  refine mem_etaleTopology_over_of_etale_of_jointlySurjective s.B s.S s.hS _ _
    (fun k ↦ hjet k.down) fun t' ↦ ?_
  obtain ⟨t, rfl⟩ := hiSurj t'
  obtain ⟨u, hu⟩ := hjhit t
  exact ⟨⟨t⟩, u, hu⟩

end AlgebraicGeometry.Space

end

