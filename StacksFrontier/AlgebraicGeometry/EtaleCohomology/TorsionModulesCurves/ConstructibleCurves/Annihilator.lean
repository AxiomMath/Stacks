module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteTypeLocallyConstantModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.PrimeToTorsion
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.ConstructibleCompactImage

/-!
# A constructible sheaf, torsion prime to `p`, is killed by an integer prime to `p`

Let `X` be a quasi-compact scheme and `ℱ` a constructible sheaf of `Λ`-modules on `X_étale`
which is torsion prime to an integer `p`: every local section is, locally, killed by a positive
integer prime to `p`. Then a single positive integer `n` prime to `p` kills `ℱ`. This is the
first step of the proof of Stacks 0GJI, which writes `ℱ` as a finite direct sum of sheaves killed
by prime powers.

## Main results

* `Stacks.EtaleCohomology.exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule` — the statement
  above, in the model `Stacks.EtaleCohomology.EtaleModules Λ X`.
* `Stacks.EtaleCohomology.exists_nsmul_eq_zero_etaleStalk_of_isConstructibleModuleSheaf` — its
  stalkwise form on the small étale site of Tag 021B.
* `Stacks.EtaleCohomology.exists_nsmul_eq_zero_etaleStalk_of_isFiniteTypeLocallyConstant` — the
  same for a finite type locally constant sheaf on a quasi-compact scheme.
* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_forall_etaleStalk` — a sheaf of modules all of whose
  geometric stalks are killed by `n` is killed by `n`.
* `Stacks.EtaleCohomology.exists_nsmul_eq_zero_presheafFiber` — at a point of a site, germs of
  locally annihilated sections are annihilated.

## Implementation notes

The argument is stalkwise, on the small étale site of Tag 021B where constructibility is defined.
The geometric stalks are finite modules all of whose elements are killed by integers prime to
`p`, so each is killed by one such integer; the point is uniformity. On a stratum the sheaf is
locally constant of finite type, so near every point its stalks are one fixed finite module, and
the stratum, being a constructible subset of an affine open, is quasi-compact; finitely many
neighbourhoods suffice. A quasi-compact `X` is covered by finitely many affine opens, each with
finitely many strata, and the product of the integers so obtained kills every geometric stalk,
hence the sheaf.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w s u r

namespace Stacks.EtaleCohomology

section Germs

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  {Λ : Type r} [Ring Λ] [HasColimitsOfSize.{w, w} (ModuleCat.{s} Λ)]
  [PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{s} Λ))] [LocallySmall.{w} C]

/-- **Germs of locally annihilated sections are annihilated.** If every section of a presheaf of
`Λ`-modules is, on the members of some covering sieve, killed by an integer satisfying `Q`, then
every element of the fibre of the presheaf at a point of the site is killed by an integer
satisfying `Q`. -/
theorem exists_nsmul_eq_zero_presheafFiber (Q : ℕ → Prop) (P : Cᵒᵖ ⥤ ModuleCat.{s} Λ)
    (hP : ∀ (V : C) (x : P.obj (op V)), ∃ R : Sieve V, R ∈ J V ∧
      ∀ (W : C) (g : W ⟶ V), R g → ∃ n : ℕ, Q n ∧ n • P.map g.op x = 0)
    (y : (Φ.presheafFiber (A := ModuleCat.{s} Λ)).obj P) : ∃ n : ℕ, Q n ∧ n • y = 0 := by
  obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective y
  obtain ⟨R, hR, hk⟩ := hP X z
  obtain ⟨Y, f, hf, y', rfl⟩ := Φ.jointly_surjective R hR x
  obtain ⟨n, hn, hz⟩ := hk Y f hf
  refine ⟨n, hn, ?_⟩
  rw [← Φ.toPresheafFiber_w_apply f y' P z, ← map_nsmul, hz, map_zero]

end Germs

section FiniteModules

/-- If one of the integers `N j`, `j ∈ s`, kills `m`, then so does their product. -/
private theorem prod_nsmul_eq_zero {ι M : Type*} [AddMonoid M] (s : Finset ι)
    (N : ι → ℕ) {i : ι} (hi : i ∈ s) {m : M} (h : N i • m = 0) : (∏ j ∈ s, N j) • m = 0 := by
  classical
  rw [← Finset.mul_prod_erase s N hi, mul_nsmul, h, nsmul_zero]

variable {Λ : Type r} [Ring Λ] {M : Type*} [AddCommGroup M] [Module Λ M]

/-- **A finite module whose elements are each killed by an integer prime to `p` is killed by one
integer prime to `p`.** -/
theorem exists_nsmul_eq_zero_of_module_finite [Module.Finite Λ M] (p : ℕ)
    (h : ∀ m : M, ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • m = 0) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ∀ m : M, n • m = 0 := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  choose N hN0 hNp hN using h
  refine ⟨∏ x ∈ S, N x, Finset.prod_pos fun x _ => hN0 x,
    Nat.Coprime.prod_left fun x _ => hNp x, fun m => ?_⟩
  have hm : m ∈ Submodule.span Λ (S : Set M) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact prod_nsmul_eq_zero S N hx (hN x)
  | zero => exact nsmul_zero _
  | add x y _ _ hx hy => rw [nsmul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

end FiniteModules

section Stalks

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type r) [CommRing Λ]

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCatMax

/-- **A sheaf of modules on the small étale site of Tag 021B is killed by `n` as soon as all its
geometric stalks are.** -/
theorem nsmul_id_eq_zero_of_forall_etaleStalk
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ)) (n : ℕ)
    (h : ∀ (t : GeometricPoint S) (y : ((geometricPointSitePoint B S hS t).presheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj G.obj),
      n • y = 0) :
    n • 𝟙 G = 0 := by
  have hsec : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (a : G.obj.obj U), n • a = 0 := by
    intro U a
    have hcov : Presheaf.equalizerSieve (n • a) (0 : G.obj.obj U) ∈
        SmallEtale.topology B S hS U.unop := by
      refine _root_.AlgebraicGeometry.mem_topology_of_forall_geometricPointFiber_lift B S hS _
        fun t q => ?_
      have heq : (geometricPointSitePoint B S hS t).toPresheafFiber U.unop q G.obj (n • a) =
          (geometricPointSitePoint B S hS t).toPresheafFiber U.unop q G.obj 0 := by
        rw [map_nsmul, h, map_zero]
      obtain ⟨V, g, y, hfiber, hsection⟩ :=
        ((geometricPointSitePoint B S hS t).toPresheafFiber_eq_iff' U.unop q _ _).mp heq
      exact ⟨V, g, hsection, y, hfiber⟩
    exact G.property.isSeparated _ _ hcov _ _ fun _ _ hf => hf
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_nsmul, Functor.map_zero, (sheafToPresheaf _ _).map_id]
  ext U a
  simpa using hsec U a

/-- **A uniform annihilator on a quasi-compact scheme for a locally constant sheaf of finite
type.** Let `H` be a finite type locally constant sheaf of `Λ`-modules on the small étale site
of Tag 021B of a quasi-compact scheme `S`, every element of every geometric stalk of which is
killed by a positive integer prime to `p`. Then one positive integer prime to `p` kills every
geometric stalk of `H`. -/
theorem exists_nsmul_eq_zero_etaleStalk_of_isFiniteTypeLocallyConstant [CompactSpace S]
    (p : ℕ) (H : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B S hS) H)
    (htors : ∀ (t : GeometricPoint S) (y : ((geometricPointSitePoint B S hS t).presheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj H.obj), ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • y = 0) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ∀ (t : GeometricPoint S)
      (y : ((geometricPointSitePoint B S hS t).presheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj H.obj), n • y = 0 := by
  classical
  choose V x E hE ψ hinj hsurj using fun z : S =>
    exists_locallyBijective_constantHom_of_isFiniteTypeLocallyConstantModuleSheaf B S hS Λ H hH
      (GeometricPoint.ofPoint S z)
  have hbij := fun z : S => bijective_moduleConstantGerm B S hS Λ (GeometricPoint.ofPoint S z)
    (x z) (ψ z) (hinj z) (hsurj z)
  have hkillE : ∀ z, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ ∀ e : E z, m • e = 0 := by
    intro z
    have : Module.Finite Λ (E z) := (ModuleCat.isFG_iff (E z)).1 (hE z)
    refine exists_nsmul_eq_zero_of_module_finite (Λ := Λ) p fun e => ?_
    obtain ⟨m, hm0, hmp, hm⟩ := htors _ (moduleConstantGerm B S hS Λ _ (x z) (ψ z) e)
    refine ⟨m, hm0, hmp, (hbij z).1 ?_⟩
    rw [map_nsmul]
    exact hm.trans (moduleConstantGerm B S hS Λ _ (x z) (ψ z)).hom.map_zero.symm
  choose m hm0 hmp hm using hkillE
  let O : S → Set S := fun z => Set.range (B.inclusion.map (V z).obj.hom).base
  have hOopen : ∀ z, IsOpen (O z) := fun z => (B.inclusion.map (V z).obj.hom).isOpenMap.isOpen_range
  have hOmem : ∀ z, z ∈ O z := fun z => ⟨(x z).1.base default,
    (congrArg (fun φ => φ.base (default : (GeometricPoint.ofPoint S z).source)) (x z).2).trans
      (GeometricPoint.ofPoint_liesOver S z)⟩
  obtain ⟨Z, hZ⟩ := isCompact_univ.elim_finite_subcover O hOopen
    fun z _ => Set.mem_iUnion.2 ⟨z, hOmem z⟩
  refine ⟨∏ z ∈ Z, m z, Finset.prod_pos fun z _ => hm0 z,
    Nat.Coprime.prod_left fun z _ => hmp z, fun t y => ?_⟩
  obtain ⟨z, hz, v, hv⟩ : ∃ z ∈ Z, t.hom.base default ∈ O z := by
    simpa using hZ (Set.mem_univ (t.hom.base default))
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (B.inclusion.map (V z).obj.hom) t.hom v hv
  let q : (geometricPointFiber B S hS t).obj (V z) := ⟨l, hl⟩
  obtain ⟨e, rfl⟩ := (bijective_moduleConstantGerm B S hS Λ t q (ψ z) (hinj z) (hsurj z)).2 y
  exact (map_nsmul _ _ e).symm.trans (by
    rw [prod_nsmul_eq_zero Z m hz (hm z e)]
    exact (moduleConstantGerm B S hS Λ t q (ψ z)).hom.map_zero)

end Stalks

section Constructible

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

/-- The pieces of a constructible stratification of an affine open are quasi-compact. -/
theorem compactSpace_piece {X : B.Scheme} (U : X.obj.affineOpens)
    (st : ConstructibleStratification B X U.1) (i : Fin st.n) :
    CompactSpace (st.piece i).obj := by
  have : CompactSpace (U.1 : Set X.obj) := isCompact_iff_compactSpace.1 U.2.isCompact
  have hc : IsCompact ((U.1.ι.base) '' (U.1.ι.base ⁻¹' Set.range
      (B.inclusion.map (st.inclusion i)).base)) :=
    ((st.constructible i).isCompact).image (U.1.ι.base.hom.continuous)
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
    Set.inter_eq_left.2 (st.contained i)] at hc
  have := st.isImmersion i
  have hemb : Topology.IsEmbedding (B.inclusion.map (st.inclusion i)).base :=
    (B.inclusion.map (st.inclusion i)).isEmbedding
  exact ⟨by rw [hemb.isCompact_iff, Set.image_univ]; exact hc⟩

/-- An isomorphism of modules carries "every element is killed by an integer satisfying `Q`". -/
private theorem exists_nsmul_eq_zero_of_iso {M N : ModuleCat.{max (u + 1) r} Λ} (e : M ≅ N)
    (Q : ℕ → Prop) (h : ∀ m : M, ∃ n : ℕ, Q n ∧ n • m = 0) (y : N) :
    ∃ n : ℕ, Q n ∧ n • y = 0 := by
  obtain ⟨n, hn, h0⟩ := h (e.inv y)
  refine ⟨n, hn, ?_⟩
  have := congrArg e.hom.hom h0
  rwa [map_nsmul, map_zero, ← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply] at this

/-- **A uniform annihilator for a constructible sheaf on a quasi-compact scheme.** Let `G` be a
constructible sheaf of `Λ`-modules on the small étale site of Tag 021B of a quasi-compact scheme
`X`, every element of every geometric stalk of which is killed by a positive integer prime to
`p`. Then one positive integer prime to `p` kills every geometric stalk of `G`. -/
theorem exists_nsmul_eq_zero_etaleStalk_of_isConstructibleModuleSheaf (X : B.Scheme)
    [CompactSpace X.obj] (p : ℕ)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G)
    (htors : ∀ (t : GeometricPoint X.obj)
      (y : ((geometricPointSitePoint B X.obj X.property t).presheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G.obj), ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • y = 0) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ∀ (t : GeometricPoint X.obj)
      (y : ((geometricPointSitePoint B X.obj X.property t).presheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj G.obj), n • y = 0 := by
  classical
  let : HasProducts.{u} (ModuleCat.{max (u + 1) r} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  obtain ⟨Us, hUs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.obj.affineOpens => (U.1 : Set X.obj)) (fun U => U.1.isOpen)
    (fun x _ => by
      have h : x ∈ (⊤ : X.obj.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X.obj] at h
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp h
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  choose st hst using hG
  have hiso : ∀ (U : X.obj.affineOpens) (i : Fin (st U).n)
      (t' : GeometricPoint ((st U).piece i).obj) (t : GeometricPoint X.obj),
      (t'.map (B.inclusion.map ((st U).inclusion i))).hom default = t.hom default →
      Nonempty (((geometricPointSitePoint B _ ((st U).piece i).property t').presheafFiber
          (A := ModuleCat.{max (u + 1) r} Λ)).obj
            (((AlgebraicGeometry.smallEtaleBaseChange B ((st U).inclusion i)).sheafPullback
              (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B ((st U).piece i).obj ((st U).piece i).property)).obj G).obj ≅
        ((geometricPointSitePoint B X.obj X.property t).presheafFiber
          (A := ModuleCat.{max (u + 1) r} Λ)).obj G.obj) := fun U i t' t hbase =>
    ⟨(smallEtalePullbackSheafFiberIso B ((st U).inclusion i) t'
        (ModuleCat.{max (u + 1) r} Λ)).app G ≪≫
      (etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase
        (ModuleCat.{max (u + 1) r} Λ)).app G.obj⟩
  choose N hN0 hNp hN using fun (U : X.obj.affineOpens) (i : Fin (st U).n) =>
    have := compactSpace_piece B U (st U) i
    exists_nsmul_eq_zero_etaleStalk_of_isFiniteTypeLocallyConstant B _ _ Λ p _
      (hst U i) fun t' y => by
        obtain ⟨e⟩ := hiso U i t' _ rfl
        obtain ⟨n, ⟨hn0, hnp⟩, hn⟩ := exists_nsmul_eq_zero_of_iso.{u, r} Λ e.symm
          (fun n => 0 < n ∧ n.Coprime p)
          (fun m => (htors _ m).imp fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) y
        exact ⟨n, hn0, hnp, hn⟩
  refine ⟨∏ U ∈ Us, ∏ i, N U i, Finset.prod_pos fun U _ => Finset.prod_pos fun i _ => hN0 U i,
    Nat.Coprime.prod_left fun U _ => Nat.Coprime.prod_left fun i _ => hNp U i, fun t y => ?_⟩
  obtain ⟨U, hU, htU⟩ : ∃ U ∈ Us, t.hom default ∈ (U.1 : Set X.obj) := by
    simpa using hUs (Set.mem_univ (t.hom default))
  obtain ⟨i, z, hz⟩ : ∃ (i : Fin (st U).n) (z : ((st U).piece i).obj),
      (B.inclusion.map ((st U).inclusion i)).base z = t.hom default := by
    have hx : t.hom default ∈ ⋃ i, Set.range (B.inclusion.map ((st U).inclusion i)).base := by
      rw [← (st U).covers]; exact htU
    exact Set.mem_iUnion.mp hx
  set t' := GeometricPoint.ofPoint ((st U).piece i).obj z
  have hbase : (t'.map (B.inclusion.map ((st U).inclusion i))).hom default = t.hom default := by
    change (B.inclusion.map ((st U).inclusion i)).base (t'.hom default) = t.hom default
    rwa [show t'.hom default = z from GeometricPoint.ofPoint_liesOver _ z]
  obtain ⟨e⟩ := hiso U i t' t hbase
  obtain ⟨n, hn, hy⟩ := exists_nsmul_eq_zero_of_iso.{u, r} Λ e (fun n => n = ∏ U ∈ Us, ∏ i, N U i)
    (fun m => ⟨_, rfl, prod_nsmul_eq_zero Us (fun U => ∏ i, N U i) hU
      (prod_nsmul_eq_zero Finset.univ (N U) (Finset.mem_univ i) (hN U i t' m))⟩) y
  rwa [← hn]

end Constructible

section EtaleModules

variable (Λ : Type r) [CommRing Λ]

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize
  AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCatMax

/-- **Torsion prime to `p` on the small étale site of Tag 021B.** The restriction of a sheaf of
`Λ`-modules which is torsion prime to `p` to the small étale site of Tag 021B of a big étale site
satisfies the same local condition there. -/
theorem isTorsionPrimeTo_etaleModuleToBoundedSite {X : Scheme.{u}} (B : BigEtaleSite.{u})
    (hX : B.Contains X) (p : ℕ) (F : EtaleModules.{u, r} Λ X)
    (hF : IsTorsionPrimeToEtaleModule Λ p X F) (V : SmallEtale B X hX)
    (x : ((etaleModuleToBoundedSite Λ B hX).obj F).obj.obj (op V)) :
    ∃ R : Sieve V, R ∈ SmallEtale.topology B X hX V ∧ ∀ (W : SmallEtale B X hX) (g : W ⟶ V),
      R g → ∃ n : ℕ, (0 < n ∧ n.Coprime p) ∧
        n • ((etaleModuleToBoundedSite Λ B hX).obj F).obj.map g.op x = 0 := by
  obtain ⟨R, hR, hk⟩ := hF ((SmallEtale.toEtaleSite B X hX).obj V) x
  refine ⟨R.functorPullback (SmallEtale.toEtaleSite B X hX),
    (SmallEtale.toEtaleSite B X hX).cover_lift (SmallEtale.topology B X hX)
      X.smallEtaleTopology hR, fun W g hg => ?_⟩
  obtain ⟨n, hn0, hnp, hn⟩ := hk _ _ hg
  exact ⟨n, ⟨hn0, hnp⟩, hn⟩

/-- **A constructible sheaf, torsion prime to `p`, on a quasi-compact scheme is killed by a
positive integer prime to `p`** (the first step of the proof of Stacks 0GJI). -/
theorem exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule {X : Scheme.{u}} [CompactSpace X]
    (p : ℕ) (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F)
    (hFp : IsTorsionPrimeToEtaleModule Λ p X F) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ n • 𝟙 F = 0 := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  let G := (etaleModuleToBoundedSite Λ B hX).obj F
  have : CompactSpace (B.obj X hX).obj := inferInstanceAs (CompactSpace X)
  obtain ⟨n, hn0, hnp, hn⟩ := exists_nsmul_eq_zero_etaleStalk_of_isConstructibleModuleSheaf B Λ
    (B.obj X hX) p G hF fun t y => by
      obtain ⟨n, ⟨hn0, hnp⟩, hn⟩ := exists_nsmul_eq_zero_presheafFiber
        (geometricPointSitePoint B X hX t) (fun n => 0 < n ∧ n.Coprime p) G.obj
        (isTorsionPrimeTo_etaleModuleToBoundedSite Λ B hX p F hFp) y
      exact ⟨n, hn0, hnp, hn⟩
  have hG : n • 𝟙 G = 0 := nsmul_id_eq_zero_of_forall_etaleStalk B X hX Λ G n hn
  refine ⟨n, hn0, hnp, ?_⟩
  let E := SmallEtale.sheafEquiv B X hX (ModuleCat.{max (u + 1) r} Λ)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let e : E.functor.obj G ≅ F := E.counitIso.app F
  calc n • 𝟙 F = e.inv ≫ (n • 𝟙 (E.functor.obj G)) ≫ e.hom := by
        rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, e.inv_hom_id]
    _ = 0 := by
      rw [← E.functor.map_id, ← Functor.map_nsmul, hG, Functor.map_zero, zero_comp, comp_zero]

end EtaleModules

end Stacks.EtaleCohomology

end
