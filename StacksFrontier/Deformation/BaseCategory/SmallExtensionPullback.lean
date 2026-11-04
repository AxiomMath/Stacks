module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct

/-!
# Pullbacks of small extensions

Base change along any morphism of `𝒞_Λ` preserves small extensions: if `f₂ : A₂ → A` is a
small extension then the first projection of `A₁ ×_A A₂ → A₁` is again one (Stacks 06GH).

Surjectivity of the projection is Mathlib's `AlgHom.surjective_pullbackFst_of_surjective`. For
the length of the kernel, the second projection identifies `ker(A₁ ×_A A₂ → A₁)` with
`ker f₂` as modules over the fibre product; the fibre product and `A₂` have the same residue
field, because `f₂` is surjective and every element of `A₂` differs from one coming from `A₁`
by an element of the maximal ideal, so comparing lengths over the two rings leaves the length
unchanged.

## Main results

* `Deformation.ArtinianLocalAlgCat.isSmallExtension_pullback_fst`: small extensions are stable
  under pullback.

## Implementation notes

The statement is about the first projection of the categorical pullback, supplied by the
`HasPullback` instance, so that it applies to whichever pullback a consumer already has; the
proof transports the computation along the canonical isomorphism with the ring of compatible
pairs, which is where the length argument takes place. Small extensions are a condition on the
underlying morphism of bundled commutative rings, matching the predicate used for Stacks 02HS.

## References

* [Stacks Project, Tag 06GH](https://stacks.math.columbia.edu/tag/06GH)
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

section
open CategoryTheory InfinitesimalLifting IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Being a small extension is unchanged by precomposing with a ring isomorphism. -/
private theorem isSmallExtension_comp_ringEquiv
    {R S T : Type v} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsArtinianRing R]
    (e : R ≃+* S) (f : S →+* T)
    (hf : IsSmallExtension (CommRingCat.ofHom f)) :
    IsSmallExtension (CommRingCat.ofHom (f.comp e.toRingHom)) := by
  classical
  rcases hf with ⟨-, hTLoc, -, hTArt, hsurj, hlen⟩
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : Module R (RingHom.ker f) := Module.compHom (RingHom.ker f) e.toRingHom
  let equiv : RingHom.ker (f.comp e.toRingHom) ≃ₗ[R] RingHom.ker f :=
    { toFun := fun x => ⟨e x.1, RingHom.mem_ker.mpr (RingHom.mem_ker.mp x.2)⟩
      invFun := fun y => ⟨e.symm y.1, RingHom.mem_ker.mpr (by simpa using RingHom.mem_ker.mp y.2)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp
      map_add' := by intro x y; ext; exact map_add e x.1 y.1
      map_smul' := by
        intro r x; ext
        show e (r * x.1) = e r * e x.1
        exact map_mul e r x.1 }
  refine ⟨inferInstance, hTLoc, inferInstance, hTArt, hsurj.comp e.surjective, ?_⟩
  show Module.length R (RingHom.ker (f.comp e.toRingHom)) = 1
  rw [equiv.length_eq, Module.length_eq_of_surjective (M := RingHom.ker f) e.surjective]
  simpa using hlen

/-- The kernel of the first projection of the ring of compatible pairs has length one over
that ring, when the second morphism is a small extension. -/
private theorem concretePullbackFst_ker_length
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hf₂ : Function.Surjective f₂.hom)
    (h₂ : IsSmallExtension (CommRingCat.ofHom f₂.hom.toRingHom)) :
    Module.length (AlgHom.pullback f₁.hom f₂.hom)
      (RingHom.ker (AlgHom.pullbackFst f₁.hom f₂.hom).toRingHom) = 1 := by
  classical
  rcases h₂ with ⟨-, -, -, -, -, h₂len⟩
  let P := AlgHom.pullback f₁.hom f₂.hom
  let _ : IsLocalRing P := AlgHom.isLocalRing_pullback f₁.hom f₂.hom
  let q : P →ₐ[Λ] A₂ := AlgHom.pullbackSnd f₁.hom f₂.hom
  let _ : Algebra P A₂ := q.toRingHom.toAlgebra
  let _ : IsLocalHom (algebraMap P A₂) := by
    show IsLocalHom q.toRingHom
    let _ : IsLocalHom f₁.hom.toRingHom := f₁.isLocal
    exact RingHom.isLocalHom_pullbackSnd f₁.hom.toRingHom f₂.hom.toRingHom
  let _ : Module P (RingHom.ker f₂.hom.toRingHom) :=
    Module.compHom (RingHom.ker f₂.hom.toRingHom) q.toRingHom
  let toKer : RingHom.ker (AlgHom.pullbackFst f₁.hom f₂.hom).toRingHom →ₗ[P]
      RingHom.ker f₂.hom.toRingHom :=
    { toFun := fun x => ⟨q x.1, by
        show f₂.hom (q x.1) = 0
        have hc : f₁.hom (AlgHom.pullbackFst f₁.hom f₂.hom x.1) = f₂.hom (q x.1) := x.1.2
        have hx : AlgHom.pullbackFst f₁.hom f₂.hom x.1 = 0 := RingHom.mem_ker.mp x.2
        rw [hx, map_zero] at hc
        exact hc.symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hbij : Function.Bijective toKer := by
    refine ⟨fun x y hxy => Subtype.ext <| Subtype.ext <| Prod.ext ?_ ?_, fun y => ?_⟩
    · exact (RingHom.mem_ker.mp x.2).trans (RingHom.mem_ker.mp y.2).symm
    · exact congrArg Subtype.val hxy
    · refine ⟨⟨⟨(0, y.1), ?_⟩, ?_⟩, rfl⟩
      · show f₁.hom 0 = f₂.hom y.1
        have hy : f₂.hom y.1 = 0 := RingHom.mem_ker.mp y.2
        simp [hy]
      · simp [AlgHom.pullbackFst]
  have hresidueSurj : Function.Surjective (algebraMap (ResidueField P) (ResidueField A₂)) := by
    intro z
    obtain ⟨a, rfl⟩ := residue_surjective (R := A₂) z
    let z₁ : ResidueField A₁ := A₁.residueEquiv.symm (A₂.residueEquiv (residue A₂ a))
    obtain ⟨a₁, ha₁⟩ := residue_surjective (R := A₁) z₁
    have hres : residue A (f₁.hom a₁) = residue A (f₂.hom a) := by
      apply A.residueEquiv.injective
      rw [f₁.residue_comm, f₂.residue_comm, ha₁]
      simp [z₁]
    have hdiff : f₁.hom a₁ - f₂.hom a ∈ maximalIdeal A :=
      (residue_eq_zero_iff _).mp (by rw [map_sub, hres, sub_self])
    obtain ⟨b, hb⟩ := hf₂ (f₁.hom a₁ - f₂.hom a)
    have hbmax : b ∈ maximalIdeal A₂ := by
      rw [← IsLocalRing.maximalIdeal_comap f₂.hom.toRingHom]
      show f₂.hom b ∈ maximalIdeal A
      rw [hb]
      exact hdiff
    let x : P := ⟨(a₁, a + b), by
      show f₁.hom a₁ = f₂.hom (a + b)
      rw [map_add, hb]
      abel⟩
    refine ⟨residue P x, ?_⟩
    show residue A₂ (q x) = residue A₂ a
    show residue A₂ (a + b) = residue A₂ a
    have hbzero : residue A₂ b = 0 := (residue_eq_zero_iff _).2 hbmax
    rw [map_add, hbzero, add_zero]
  change Module.length A₂ (RingHom.ker f₂.hom.toRingHom) = 1 at h₂len
  rw [(LinearEquiv.ofBijective toKer hbij).length_eq,
    IsLocalRing.length_restrictScalars P A₂ (RingHom.ker f₂.hom.toRingHom),
    h₂len, Module.length_eq_of_surjective (M := ResidueField A₂) hresidueSurj]
  simp

/-- The first projection of the ring of compatible pairs is a small extension when the second
morphism is. -/
private theorem concretePullbackFst_isSmallExtension
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (h : IsConcretePullback f₁ f₂)
    (h₂ : IsSmallExtension (CommRingCat.ofHom f₂.hom.toRingHom)) :
    IsSmallExtension (CommRingCat.ofHom h.fst.hom.toRingHom) := by
  cases h.obj_carrier
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · show Function.Surjective h.fst.hom
    rw [h.fst_hom]
    exact AlgHom.surjective_pullbackFst_of_surjective f₁.hom f₂.hom h₂.2.2.2.2.1
  · show Module.length h.obj (RingHom.ker h.fst.hom.toRingHom) = 1
    rw [h.fst_hom]
    exact concretePullbackFst_ker_length f₁ f₂ h₂.2.2.2.2.1 h₂

/-- The first projection from the pullback of a small extension in `𝒞_Λ` is a small
extension. -/
@[stacks 06GH "pullback_small_extension"]
theorem isSmallExtension_pullback_fst
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A) [Limits.HasPullback f₁ f₂]
    (h₂ : IsSmallExtension (CommRingCat.ofHom f₂.hom.toRingHom)) :
    IsSmallExtension
      (CommRingCat.ofHom (Limits.pullback.fst f₁ f₂).hom.toRingHom) := by
  classical
  let c := (hasPullback_of_surjective f₁ f₂ (Or.inr h₂.2.2.2.2.1)).1
  let iso := c.isPullback.isoPullback
  have hom_congr {X Y : ArtinianLocalAlgCat.{u, v, w} Λ k} {g g' : X ⟶ Y} (h : g = g')
      (x : X) : g.hom x = g'.hom x := by rw [h]
  let e : (↑(Limits.pullback f₁ f₂)) ≃+* ↑c.obj :=
    { toFun := iso.inv.hom
      invFun := iso.hom.hom
      left_inv := hom_congr (Iso.inv_hom_id iso)
      right_inv := hom_congr (Iso.hom_inv_id iso)
      map_mul' := map_mul iso.inv.hom
      map_add' := map_add iso.inv.hom }
  have heq : c.fst.hom.toRingHom.comp e.toRingHom =
      (Limits.pullback.fst f₁ f₂).hom.toRingHom := by
    ext x
    show c.fst.hom (iso.inv.hom x) = (Limits.pullback.fst f₁ f₂).hom x
    exact hom_congr c.isPullback.isoPullback_inv_fst x
  simpa only [heq] using isSmallExtension_comp_ringEquiv e c.fst.hom.toRingHom
    (concretePullbackFst_isSmallExtension f₁ f₂ c h₂)

end

end ArtinianLocalAlgCat

end Deformation

end
