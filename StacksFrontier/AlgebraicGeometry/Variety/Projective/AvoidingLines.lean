module

public import Mathlib.Algebra.MvPolynomial.Funext
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksCore.Tactic.StacksAttribute

/-!
# Lines through a point avoiding a closed subvariety of codimension two

Let `V` be a nonzero finite-dimensional vector space over an algebraically closed field `k`, let
`B ⊆ 𝐏(V)` be an irreducible closed subset of codimension at least two and let `p` be a closed
point of `𝐏(V)` outside `B`. Projecting away from `p` carries `B` to a closed subset
`r_p(B) ⊆ 𝐏(W_p)` of dimension at most `dim B ≤ dim 𝐏(V) - 2 < dim 𝐏(W_p)`, so `r_p(B)` is a
proper closed subset. A closed point of its complement is a corank-one subspace of `W_p`, that
is a line through `p`, and that line misses `B`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_toSpecZero` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.projection_comp_toSpec`: the linear projection is a
  morphism of schemes over the ground field.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_projectiveSpaceOfModuleToSpec`: the
  projective space of a nonzero finite-dimensional vector space is proper over the ground field.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionDomain`: the domain of definition of the
  linear projection away from the linear subspace cut out by a submodule.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.gradedZeroRingHom_comp_algebraMap`: the inclusion of
  a submodule induces a `k`-algebra homomorphism of symmetric algebras.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_projection`: a closed subset disjoint
  from that linear subspace has closed image under the projection.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_line_disjoint_of_codimension_ge_two`: a
  projective line through `p` disjoint from `B`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_subset_union_lines_disjoint`: a
  nonempty open subset of `𝐏(V)` whose closed points all lie on such a line.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_line_disjoint_and_isOpen_sweep`: both
  statements of the tag at once, with the open subset pinned down as the one whose closed points
  other than `p` are exactly those swept out by the avoiding lines through `p`.

## References

* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

universe u

variable {A B σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The morphism induced by a graded ring homomorphism is a morphism over `Spec` of the
degree-zero parts.** This is the partially defined analogue of
`AlgebraicGeometry.Proj.map_toSpecZero`: the square formed by `mapHom`, the two structure
morphisms `AlgebraicGeometry.Proj.toSpecZero` and `Spec` of the degree-zero component of the
homomorphism commutes on the domain of definition. -/
@[ega "II 3.5.6" "special case"]
public theorem mapHom_toSpecZero (ψ : 𝒜 →+*ᵍ ℬ) :
    mapHom 𝒜 ℬ ψ ≫ Proj.toSpecZero 𝒜 =
      (mapDomain 𝒜 ℬ ψ).ι ≫ Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom ψ.gradedZeroRingHom) := by
  refine mapDomain_hom_ext 𝒜 ℬ ψ _ _ fun d hd f hf => ?_
  have hι : (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) ≫
      (mapDomain 𝒜 ℬ ψ).ι =
      Proj.basicOpenToSpec ℬ (ψ f) ≫ Proj.awayι ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd := by
    rw [Scheme.homOfLE_ι, ← Proj.basicOpenIsoSpec_hom ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd,
      Proj.awayι, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, homOfLE_mapHom 𝒜 ℬ ψ hd hf, mapAwayHom, reassoc_of% hι]
  simp only [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [Proj.awayMap_comp_fromZeroRingHom (𝒜 := 𝒜) (ℬ := ℬ) ψ f]

end Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

open Stacks.AlgebraicGeometry.ProjTwistChain

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The open subscheme of `𝐏(V)` on which the projection away from the linear subspace cut out
by a submodule `W` of `V` is defined, namely the complement of that linear subspace. -/
public abbrev projectionDomain (W : Submodule k V) : (projectiveSpaceOfModule k V).Opens :=
  mapDomain (fun n => SymPow.symmetricPower n k ↥W) (fun n => SymPow.symmetricPower n k V)
    (SymPow.gradedSymAlgMap W.subtype)

/-- The degree-zero part of the graded homomorphism induced by the inclusion of a submodule is
the identity on the ground field: the induced map of symmetric algebras is a `k`-algebra
homomorphism. -/
public theorem gradedZeroRingHom_comp_algebraMap (W : Submodule k V) :
    (SymPow.gradedSymAlgMap W.subtype).gradedZeroRingHom.comp
        (algebraMap k ↥(SymPow.symmetricPower 0 k ↥W)) =
      algebraMap k ↥(SymPow.symmetricPower 0 k V) :=
  RingHom.ext fun r => Subtype.ext ((SymPow.symAlgMap W.subtype).commutes r)

/-- **The linear projection away from `W` is a morphism of schemes over the ground field.** -/
public theorem projection_comp_toSpec (W : Submodule k V) :
    projection k V W ≫ projectiveSpaceOfModuleToSpec k ↥W =
      (projectionDomain k V W).ι ≫ projectiveSpaceOfModuleToSpec k V := by
  rw [projectiveSpaceOfModuleToSpec, projectiveSpaceOfModuleToSpec, projection,
    ← Category.assoc, mapHom_toSpecZero, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, gradedZeroRingHom_comp_algebraMap]

/-- **The projective space of a nonzero finite-dimensional vector space is proper over the
ground field**, being isomorphic over `Spec k` to projective `n`-space. -/
public instance isProper_projectiveSpaceOfModuleToSpec [FiniteDimensional k V] [Nontrivial V] :
    IsProper (projectiveSpaceOfModuleToSpec k V) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := k) (M := V)).ne'
  let e := (Over.forget (Spec (CommRingCat.of k))).mapIso
    (basisProjectiveSpaceOfModuleIso (Module.finBasisOfFinrankEq k V hn))
  have hw : e.hom ≫ (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
      projectiveSpaceOfModuleToSpec k V := Over.w _
  have hP : IsProper (projectiveSpaceOverRing n (CommRingCat.of k) ↘
    Spec (CommRingCat.of k)) := inferInstance
  rw [← hw]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) e.hom _).2 hP

/-- **A closed subset disjoint from the linear subspace cut out by `W` is the image of a scheme
proper over `𝐏(W)` and no larger than the subset.** The closed subscheme cut out by the subset
lies in the domain of the projection away from `W`, so the projection restricts to it as a
morphism to `𝐏(W)` which is proper over the ground field and has the projected subset as image. -/
private theorem exists_isProper_range_eq_image_projection [FiniteDimensional k V] [Nontrivial V]
    (W : Submodule k V) [Nontrivial ↥W]
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCW : Disjoint C (linearSubspace k V W)) :
    ∃ (X : Scheme.{u}) (f : X ⟶ projectiveSpaceOfModule k ↥W), IsProper f ∧
      Set.range f.base =
        (projection k V W).base '' ((projectionDomain k V W).ι.base ⁻¹' C) ∧
      topologicalKrullDim X ≤ topologicalKrullDim C := by
  set I : (projectiveSpaceOfModule k V).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩ with hI
  have hrange : Set.range I.subschemeι.base = C := by
    rw [hI, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hsub : Set.range I.subschemeι.base ⊆ Set.range (projectionDomain k V W).ι.base := by
    rw [hrange, Scheme.Opens.range_ι, coe_mapDomain_subtype]
    exact Set.subset_compl_iff_disjoint_right.mpr hCW
  set j := IsOpenImmersion.lift (projectionDomain k V W).ι I.subschemeι hsub with hj
  have hjfac : j ≫ (projectionDomain k V W).ι = I.subschemeι :=
    IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ y, (projectionDomain k V W).ι.base (j.base y) = I.subschemeι.base y := by
    intro y
    rw [← hjfac, Scheme.Hom.comp_base]
    rfl
  have hinj : Function.Injective (projectionDomain k V W).ι.base :=
    (projectionDomain k V W).ι.isOpenEmbedding.injective
  have hrj : Set.range j.base = (projectionDomain k V W).ι.base ⁻¹' C := by
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, rfl⟩
      rw [Set.mem_preimage, hcomp, ← hrange]
      exact ⟨y, rfl⟩
    · obtain ⟨y, hy⟩ : (projectionDomain k V W).ι.base x ∈ Set.range I.subschemeι.base := by
        rwa [hrange]
      exact ⟨y, hinj (by rw [hcomp, hy])⟩
  have h2 : IsProper ((j ≫ projection k V W) ≫ projectiveSpaceOfModuleToSpec k ↥W) := by
    rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hjfac]
    infer_instance
  refine ⟨I.subscheme, j ≫ projection k V W,
    IsProper.of_comp _ (projectiveSpaceOfModuleToSpec k ↥W), ?_, ?_⟩
  · rw [← hrj]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  · refine Topology.IsInducing.topologicalKrullDim_le (f := fun x : I.subscheme =>
      (⟨I.subschemeι.base x, hrange ▸ Set.mem_range_self x⟩ : ↥C)) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact I.subschemeι.isClosedEmbedding.isInducing

/-- **The image of a closed subset under the linear projection is closed.** A closed subset of
`𝐏(V)` disjoint from the linear subspace cut out by `W` lies in the domain of the projection
away from `W`, is proper over the ground field, and so has closed image in `𝐏(W)`. -/
public theorem isClosed_image_projection [FiniteDimensional k V] [Nontrivial V]
    (W : Submodule k V) [Nontrivial ↥W]
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCW : Disjoint C (linearSubspace k V W)) :
    IsClosed ((projection k V W).base '' ((projectionDomain k V W).ι.base ⁻¹' C)) := by
  obtain ⟨X, f, hf, hrange, -⟩ := exists_isProper_range_eq_image_projection k V W hC hCW
  rw [← hrange]
  exact f.isClosedMap.isClosed_range

/-- A nonzero element of `Sym V` is not killed by every nonzero linear functional on `V`: read
through a basis it is a nonzero polynomial, and a nonzero polynomial over an infinite field has
a nonvanishing point, which can be taken away from the origin. -/
public theorem exists_dual_symAlgMap_ne_zero [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] {h : SymmetricAlgebra k V} (hh : h ≠ 0) :
    ∃ (f : Module.Dual k V) (_ : f ≠ 0), SymPow.symAlgMap f h ≠ 0 := by
  classical
  set b := Module.Free.chooseBasis k V with hb
  have hfin : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  have : Fintype (Module.Free.ChooseBasisIndex k V) := Fintype.ofFinite _
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex k V) := b.index_nonempty
  set e := SymmetricAlgebra.equivMvPolynomial b with he
  have hP : e h ≠ 0 := fun h0 => hh (by simpa using e.injective (h0.trans (map_zero e).symm))
  have hP' : e h * MvPolynomial.X i₀ ≠ 0 := mul_ne_zero hP (MvPolynomial.X_ne_zero i₀)
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (e h * MvPolynomial.X i₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hP' (MvPolynomial.funext fun x => by simpa using hc x)
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_X] at hx
  have hxi : x i₀ ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
  have hev : MvPolynomial.eval x (e h) ≠ 0 := fun h0 => hx (by rw [h0, zero_mul])
  set f : Module.Dual k V := b.dualBasis.equivFun.symm x with hf
  have hfv (i) : f (b i) = x i := by
    have hc := congrFun (b.dualBasis.equivFun.apply_symm_apply x) i
    simpa [hf, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr] using hc
  have hf0 : f ≠ 0 := fun h0 => hxi (by rw [← hfv i₀, h0, LinearMap.zero_apply])
  have hmaps : (MvPolynomial.aeval x).comp e.toAlgHom = SymmetricAlgebra.lift f := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    have hlin : f = (MvPolynomial.aeval x).toLinearMap.comp
        (e.toLinearMap.comp (SymmetricAlgebra.ι k V)) := by
      apply b.ext
      intro i
      rw [hfv i]
      simp [he, SymmetricAlgebra.equivMvPolynomial_ι_apply]
    have hpoint : (MvPolynomial.aeval x) (e (SymmetricAlgebra.ι k V w)) = f w :=
      (congrArg (fun g : Module.Dual k V => g w) hlin).symm
    convert hpoint using 1 <;> simp
  have hcomp : (SymmetricAlgebra.lift (LinearMap.id : k →ₗ[k] k)).comp
      (SymPow.symAlgMap f) = SymmetricAlgebra.lift f := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    simp [SymPow.symAlgMap]
  refine ⟨f, hf0, fun hzero => hev ?_⟩
  have h1 : SymmetricAlgebra.lift f h = 0 := by
    rw [← hcomp]
    simp [hzero]
  have h2 : (MvPolynomial.aeval x) (e h) = SymmetricAlgebra.lift f h :=
    congrArg (fun g : SymmetricAlgebra k V →ₐ[k] k => g h) hmaps
  rw [show MvPolynomial.eval x (e h) = (MvPolynomial.aeval x) (e h) from rfl, h2, h1]

/-- **The image of a closed subset under the linear projection has dimension at most that of the
subset.** The closed subscheme cut out by the subset maps properly to `𝐏(W)`, so the restriction
of the projection to it is a continuous closed surjection onto the image; specializations lift
along a closed map, so [Stacks, Tag 02JF] bounds the dimension of the image, and the closed
subscheme is homeomorphic onto the subset. -/
private theorem topologicalKrullDim_image_projection_le [FiniteDimensional k V] [Nontrivial V]
    (W : Submodule k V) [Nontrivial ↥W]
    {C : Set (projectiveSpaceOfModule k V)} (hC : IsClosed C)
    (hCW : Disjoint C (linearSubspace k V W)) :
    topologicalKrullDim ((projection k V W).base '' ((projectionDomain k V W).ι.base ⁻¹' C)) ≤
      topologicalKrullDim C := by
  obtain ⟨X, f, hf, hrange, hdim⟩ := exists_isProper_range_eq_image_projection k V W hC hCW
  have hmclosed : IsClosedMap f.base := f.isClosedMap
  rw [← hrange]
  refine le_trans ?_ hdim
  have : QuasiSober ↥(Set.range f.base) :=
    Topology.IsClosedEmbedding.quasiSober hmclosed.isClosed_range.isClosedEmbedding_subtypeVal
  refine Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    (fun x => (⟨f.base x, ⟨x, rfl⟩⟩ : ↥(Set.range f.base)))
    (by fun_prop) (fun z => ⟨z.2.choose, Subtype.ext z.2.choose_spec⟩) (Or.inl ?_)
  refine IsClosedMap.specializingMap fun F hF => ?_
  have himg : (fun x => (⟨f.base x, ⟨x, rfl⟩⟩ : ↥(Set.range f.base))) '' F =
      Subtype.val ⁻¹' (f.base '' F) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage, Subtype.ext_iff]
  rw [himg]
  exact (hmclosed F hF).preimage continuous_subtype_val

/-- **A proper closed subset of `𝐏(V)` misses a closed point.** The closed subset is the zero
locus of its vanishing ideal, which therefore has an element that some nonzero linear functional
does not kill, and the point that functional cuts out lies outside the subset. -/
public theorem exists_linearFunctionalPoint_notMem_of_ne_univ [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] {S : Set (projectiveSpaceOfModule k V)}
    (hS : IsClosed S) (hne : S ≠ Set.univ) :
    ∃ (f : Module.Dual k V) (hf : f ≠ 0), linearFunctionalPoint k V f hf ∉ S := by
  let A : ℕ → Submodule k (SymmetricAlgebra k V) := fun n => SymPow.symmetricPower n k V
  let T : Set (ProjectiveSpectrum A) := S
  have hT : IsClosed T := hS
  have hzero : ProjectiveSpectrum.zeroLocus A
      (ProjectiveSpectrum.vanishingIdeal T : Set (SymmetricAlgebra k V)) = T :=
    (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure A T).trans hT.closure_eq
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem T).mp hne
  obtain ⟨g, hgS, hgy⟩ := Set.not_subset.mp fun hsub =>
    hy (hzero ▸ (ProjectiveSpectrum.mem_zeroLocus A y _).mpr hsub)
  have hg0 : g ≠ 0 := fun h0 => hgy (h0 ▸ zero_mem _)
  obtain ⟨f, hf, hfg⟩ := exists_dual_symAlgMap_ne_zero k V hg0
  refine ⟨f, hf, fun hmem => hfg ?_⟩
  have h2 : (ProjectiveSpectrum.vanishingIdeal T : Set (SymmetricAlgebra k V)) ⊆
      (linearFunctionalPoint k V f hf).asHomogeneousIdeal := by
    refine (ProjectiveSpectrum.mem_zeroLocus A (linearFunctionalPoint k V f hf) _).mp ?_
    rw [hzero]
    exact hmem
  exact (linearFunctionalPoint_mem k V f hf g).mp (h2 hgS)

/-- **The degree-one forms vanishing at the image of a point under the projection away from `W`**
are the vectors of `W` whose images vanish at the point itself. -/
public theorem mem_pointSubmodule_projection_iff {k V : Type u} [Field k] [AddCommGroup V]
    [Module k V] {W : Submodule k V} (x : (projectionDomain k V W).toScheme) (w : ↥W) :
    w ∈ pointSubmodule k ↥W ((projection k V W).base x) ↔ (w : V) ∈ pointSubmodule k V x.1 := by
  rw [mem_pointSubmodule_iff, mem_projection_iff k V W x Nat.one_pos (by simp),
    SymPow.symAlgMap_ι]
  exact (mem_pointSubmodule_iff k V x.1 (w : V)).symm

/-- **The projection away from `W` is constant on a linear subspace through the centre.** A point
of the domain of definition lying on a linear subspace whose equations contain every vector of
`W` killed by a nonzero functional `g` projects to the point of `𝐏(W)` cut out by `g`. -/
public theorem projection_eq_linearFunctionalPoint_of_mem (W : Submodule k V)
    (y : (projectionDomain k V W).toScheme) (g : Module.Dual k ↥W) (hg : g ≠ 0)
    (W' : Submodule k V) (hW' : ∀ w : ↥W, g w = 0 → (w : V) ∈ W')
    (hy : (y.val : projectiveSpaceOfModule k V) ∈ linearSubspace k V W') :
    projection k V W y = linearFunctionalPoint k ↥W g hg := by
  have hle : LinearMap.ker g ≤ pointSubmodule k ↥W (projection k V W y) := fun w hw =>
    (mem_pointSubmodule_projection_iff y w).mpr
      ((mem_linearSubspace_iff k V W' _).mp hy (hW' w (LinearMap.mem_ker.mp hw)))
  have hmem := (mem_linearSubspace_iff k ↥W (LinearMap.ker g) _).mpr hle
  rwa [linearSubspace_ker, Set.mem_singleton_iff] at hmem

/-- The hyperplane of degree-one forms vanishing at a closed point of `𝐏(V)` has dimension one
less than `V`. -/
public theorem finrank_pointSubmodule_add_one [IsAlgClosed k] [FiniteDimensional k V]
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    Module.finrank k ↥(pointSubmodule k V p) + 1 = Module.finrank k V := by
  have h := Submodule.finrank_quotient_add_finrank (R := k) (pointSubmodule k V p)
  rw [finrank_quotient_pointSubmodule k V p hp] at h
  omega

/-- An irreducible closed subset of codimension at least two in `𝐏(V)`, where `V` has dimension
`n + 1`, has dimension at most `n - 2`. -/
private theorem topologicalKrullDim_add_two_le [IsAlgClosed k] [FiniteDimensional k V]
    {n : ℕ} (hn : Module.finrank k V = n + 1) (B : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hcodim : (2 : ℕ∞) ≤ codimension B) :
    topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) + 2 ≤ (n : WithBot ℕ∞) :=
  le_trans (add_le_add le_rfl (by simpa using WithBot.coe_le_coe.mpr hcodim))
    (topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule hn B)

/-- The hyperplane of a closed point of `𝐏(V)` has dimension at least two once `𝐏(V)` carries an
irreducible closed subset of codimension at least two, since then `V` has dimension at least
three. -/
private theorem two_le_finrank_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (B : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hcodim : (2 : ℕ∞) ≤ codimension B) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    2 ≤ Module.finrank k ↥(pointSubmodule k V p) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := k) (M := V)).ne'
  have hWrank := finrank_pointSubmodule_add_one k V p hp
  have hB0 : (0 : WithBot ℕ∞) ≤
      topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) := by
    have : Nonempty ↥(B : Set (projectiveSpaceOfModule k V)) :=
      B.isIrreducible'.nonempty.to_subtype
    have : Nonempty (IrreducibleCloseds ↥(B : Set (projectiveSpaceOfModule k V))) :=
      ⟨IrreducibleCloseds.closureSingleton (Classical.arbitrary _)⟩
    exact Order.krullDim_nonneg
  have hle := topologicalKrullDim_add_two_le k V hn B hcodim
  have h0 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) + 2 := by
    simpa using add_le_add hB0 (le_refl (2 : WithBot ℕ∞))
  have hn2 : 2 ≤ n := by exact_mod_cast le_trans h0 hle
  omega

/-- The hyperplane of a closed point is nontrivial once `𝐏(V)` carries an irreducible closed
subset of codimension at least two. -/
private theorem nontrivial_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (B : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hcodim : (2 : ℕ∞) ≤ codimension B) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    Nontrivial ↥(pointSubmodule k V p) :=
  Module.nontrivial_of_finrank_pos (R := k)
    (lt_of_lt_of_le Nat.zero_lt_two (two_le_finrank_pointSubmodule k V B hcodim p hp))

/-- A closed point outside a subset is disjoint from it, so the subset misses the linear subspace
cut out by the hyperplane of that point. -/
private theorem disjoint_linearSubspace_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    {p : projectiveSpaceOfModule k V}
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    {C : Set (projectiveSpaceOfModule k V)} (hpC : p ∉ C) :
    Disjoint C (linearSubspace k V (pointSubmodule k V p)) := by
  rw [linearSubspace_pointSubmodule k V p hp]
  exact Set.disjoint_singleton_right.mpr hpC

/-- **The image of `B` under the projection away from `p` is closed.** -/
private theorem isClosed_image_projection_pointSubmodule [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    IsClosed ((projection k V (pointSubmodule k V p)).base ''
      ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
        (B : Set (projectiveSpaceOfModule k V)))) :=
  have := nontrivial_pointSubmodule k V B hcodim p hp
  isClosed_image_projection k V (pointSubmodule k V p) B.isClosed'
    (disjoint_linearSubspace_pointSubmodule k V hp hpB)

/-- **The image of `B` under the projection away from `p` is not all of `𝐏(W_p)`.** Its dimension
is at most that of `B`, which is at least two less than the dimension of `𝐏(V)`, hence strictly
less than the dimension of `𝐏(W_p)`. -/
private theorem image_projection_ne_univ [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    (projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
          (B : Set (projectiveSpaceOfModule k V))) ≠ Set.univ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := k) (M := V)).ne'
  have hWrank : Module.finrank k ↥(pointSubmodule k V p) = n := by
    have h := finrank_pointSubmodule_add_one k V p hp
    omega
  have hle := topologicalKrullDim_add_two_le k V hn B hcodim
  have hn2 : 2 ≤ n := by
    have := two_le_finrank_pointSubmodule k V B hcodim p hp
    omega
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := nontrivial_pointSubmodule k V B hcodim p hp
  intro hcontra
  have hSdim := topologicalKrullDim_image_projection_le k V (pointSubmodule k V p)
    (C := (B : Set (projectiveSpaceOfModule k V))) B.isClosed'
    (disjoint_linearSubspace_pointSubmodule k V hp hpB)
  rw [hcontra] at hSdim
  have huniv : topologicalKrullDim
      (Set.univ : Set (projectiveSpaceOfModule k ↥(pointSubmodule k V p))) =
        (m : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
    exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by rw [hWrank, hm])
  rw [huniv] at hSdim
  have hfin : (m : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞) :=
    le_trans (add_le_add hSdim (le_refl (2 : WithBot ℕ∞))) hle
  rw [hm] at hfin
  have hbad : m + 2 ≤ m + 1 := by exact_mod_cast hfin
  omega

/-- **The line joining `p` to a closed point no point of `B` projects onto misses `B`.** Any
point of `B` on that line lies outside `p`, hence in the domain of the projection away from `p`,
and projects to the same point of `𝐏(W_p)` as the closed point does. -/
private theorem lineSubmodule_spec [IsAlgClosed k] [FiniteDimensional k V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V)))
    (y : (projectionDomain k V (pointSubmodule k V p)).toScheme)
    (hyc : IsClosed ({(y.val : projectiveSpaceOfModule k V)} :
      Set (projectiveSpaceOfModule k V)))
    (hyB : ∀ z : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      (z.val : projectiveSpaceOfModule k V) ∈ (B : Set (projectiveSpaceOfModule k V)) →
      projection k V (pointSubmodule k V p) z ≠ projection k V (pointSubmodule k V p) y) :
    Module.finrank k (V ⧸ lineSubmodule k V p y.val) = 2 ∧
      p ∈ linearSubspace k V (lineSubmodule k V p y.val) ∧
      (y.val : projectiveSpaceOfModule k V) ∈
        linearSubspace k V (lineSubmodule k V p y.val) ∧
      Disjoint (linearSubspace k V (lineSubmodule k V p y.val))
        (B : Set (projectiveSpaceOfModule k V)) := by
  have hDp : ((projectionDomain k V (pointSubmodule k V p) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) = {p}ᶜ :=
    coe_mapDomain_pointSubmodule k V p hp
  have hymem : (y.val : projectiveSpaceOfModule k V) ∈
      ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := y.2
  rw [hDp] at hymem
  obtain ⟨f, hf, hfy⟩ := exists_eq_linearFunctionalPoint k V y.val hyc
  have hgne : f ∘ₗ (pointSubmodule k V p).subtype ≠ 0 := by
    intro h0
    refine hymem ?_
    have hle : pointSubmodule k V p ≤
        pointSubmodule k V (y.val : projectiveSpaceOfModule k V) := by
      rw [hfy, pointSubmodule_linearFunctionalPoint]
      intro w hw
      exact LinearMap.mem_ker.mpr (congrArg (fun g : Module.Dual k ↥(pointSubmodule k V p) =>
        g ⟨w, hw⟩) h0)
    have hmem := (mem_linearSubspace_iff k V (pointSubmodule k V p) _).mpr hle
    rwa [linearSubspace_pointSubmodule k V p hp, Set.mem_singleton_iff] at hmem
  have hyproj : projection k V (pointSubmodule k V p) y =
      linearFunctionalPoint k ↥(pointSubmodule k V p)
        (f ∘ₗ (pointSubmodule k V p).subtype) hgne :=
    projection_eq_linearFunctionalPoint k V (pointSubmodule k V p) y f hf hgne hfy
  refine ⟨finrank_quotient_lineSubmodule k V hp hyc (Ne.symm hymem),
    left_mem_linearSubspace_lineSubmodule k V _ _,
    right_mem_linearSubspace_lineSubmodule k V _ _, Set.disjoint_left.mpr fun z hzL hzB => ?_⟩
  have hzp : z ≠ p := fun h0 => hpB (h0 ▸ hzB)
  have hzD : z ∈ ((projectionDomain k V (pointSubmodule k V p) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rwa [hDp]
  refine hyB ⟨z, hzD⟩ hzB ?_
  rw [hyproj]
  refine projection_eq_linearFunctionalPoint_of_mem k V (pointSubmodule k V p) ⟨z, hzD⟩ _ hgne
    (lineSubmodule k V p y.val) (fun v hv => ?_) hzL
  refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
  rw [hfy, pointSubmodule_linearFunctionalPoint]
  exact LinearMap.mem_ker.mpr hv

/-- **A closed point of `𝐏(V)` off `p` whose projection avoids the image of `B`.** The image of
`B` is a proper closed subset of `𝐏(W_p)`, so it misses a point cut out by a nonzero functional
on `W_p`; any extension of that functional to `V` cuts out such a closed point. -/
private theorem exists_closedPoint_projection_notMem_image [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    ∃ y : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      IsClosed ({(y.val : projectiveSpaceOfModule k V)} :
        Set (projectiveSpaceOfModule k V)) ∧
      projection k V (pointSubmodule k V p) y ∉
        (projection k V (pointSubmodule k V p)).base ''
          ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
            (B : Set (projectiveSpaceOfModule k V))) := by
  have := nontrivial_pointSubmodule k V B hcodim p hp
  obtain ⟨g, hg, hgS⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k
    ↥(pointSubmodule k V p) (isClosed_image_projection_pointSubmodule k V B hcodim p hp hpB)
    (image_projection_ne_univ k V B hcodim p hp hpB)
  obtain ⟨f, hfg⟩ := LinearMap.dualMap_surjective_of_injective
    (pointSubmodule k V p).injective_subtype g
  have hcomp : f ∘ₗ (pointSubmodule k V p).subtype = g := by
    refine LinearMap.ext fun w => ?_
    rw [← hfg, LinearMap.dualMap_apply]
    rfl
  subst hcomp
  have hf : f ≠ 0 := fun h0 => hg (by rw [h0, LinearMap.zero_comp])
  have hqD : linearFunctionalPoint k V f hf ∈
      ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_mapDomain_subtype]
    intro hmem
    refine hg (LinearMap.ext fun w => ?_)
    have hw := (mem_linearSubspace_iff k V (pointSubmodule k V p) _).mp hmem w.2
    rw [pointSubmodule_linearFunctionalPoint] at hw
    exact LinearMap.mem_ker.mp hw
  obtain ⟨y, hy⟩ : ∃ y : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf :=
    ⟨⟨linearFunctionalPoint k V f hf, hqD⟩, rfl⟩
  refine ⟨y, hy ▸ linearFunctionalPoint_isClosed k V f hf, ?_⟩
  rwa [projection_eq_linearFunctionalPoint k V (pointSubmodule k V p) y f hf hg hy]

/-- **Existence of an avoiding line.** Let `B` be an irreducible closed subset of
codimension at least two in the projective space of a nonzero finite-dimensional vector space
over an algebraically closed field, and let `p` be a closed point outside `B`. Then some
projective line through `p` is disjoint from `B`. This is the first half of [Stacks, Tag 0B2T],
whose full statement is `exists_line_disjoint_and_isOpen_sweep`. -/
public theorem exists_line_disjoint_of_codimension_ge_two [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
      p ∈ linearSubspace k V W ∧
      Disjoint (linearSubspace k V W) (B : Set (projectiveSpaceOfModule k V)) := by
  obtain ⟨y, hyc, hyS⟩ := exists_closedPoint_projection_notMem_image k V B hcodim p hp hpB
  obtain ⟨h2, hpL, -, hdisj⟩ := lineSubmodule_spec k V B p hp hpB y hyc fun z hzB heq =>
    hyS ⟨z, hzB, heq⟩
  exact ⟨lineSubmodule k V p y.val, h2, hpL, hdisj⟩

/-- **An open subset swept out by avoiding lines.** With `B` and `p` as above there
is a nonempty open subset of `𝐏(V)` each of whose closed points lies on a projective line
through `p` disjoint from `B`. This is the second half of [Stacks, Tag 0B2T], whose full
statement is `exists_line_disjoint_and_isOpen_sweep`. -/
public theorem exists_isOpen_subset_union_lines_disjoint [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k V)) →
        ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
          p ∈ linearSubspace k V W ∧ q ∈ linearSubspace k V W ∧
          Disjoint (linearSubspace k V W) (B : Set (projectiveSpaceOfModule k V)) := by
  have hSclosed := isClosed_image_projection_pointSubmodule k V B hcodim p hp hpB
  obtain ⟨y, hyc, hyS⟩ := exists_closedPoint_projection_notMem_image k V B hcodim p hp hpB
  refine ⟨(projectionDomain k V (pointSubmodule k V p)).ι.base ''
    ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
          (B : Set (projectiveSpaceOfModule k V))))ᶜ),
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isOpenMap _
      (hSclosed.isOpen_compl.preimage (by fun_prop)), ⟨y.val, y, hyS, rfl⟩, ?_⟩
  rintro q ⟨z, hzS, rfl⟩ hqc
  obtain ⟨h2, hpL, hqL, hdisj⟩ := lineSubmodule_spec k V B p hp hpB z hqc fun w hwB heq =>
    hzS ⟨w, hwB, heq⟩
  exact ⟨lineSubmodule k V p z.val, h2, hpL, hqL, hdisj⟩

/-- **Stacks 0B2T.** Let `B` be an irreducible closed subset of codimension at least two in the
projective space of a nonzero finite-dimensional vector space over an algebraically closed field
and let `p` be a closed point outside `B`. Then some projective line through `p` is disjoint
from `B`, and the closed points other than `p` lying on such a line are exactly the closed points
of a nonempty open subset of `𝐏(V)`, namely the complement of the cone over the image of `B`
under the projection away from `p`. The union of the avoiding lines itself is not open: in a
projective plane with `B` a point it contains `p` but no neighbourhood of `p`. -/
@[stacks 0B2T "the sweeping-out clause is read as the proof reads it: the avoiding lines through
`p` cover the closed points of an open subset, their union itself being non-open at `p`"]
public theorem exists_line_disjoint_and_isOpen_sweep [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hcodim : (2 : ℕ∞) ≤ codimension B)
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ (B : Set (projectiveSpaceOfModule k V))) :
    (∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧ p ∈ linearSubspace k V W ∧
        Disjoint (linearSubspace k V W) (B : Set (projectiveSpaceOfModule k V))) ∧
      ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧
        (∃ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k V))) ∧
        ∀ q, IsClosed ({q} : Set (projectiveSpaceOfModule k V)) → q ≠ p →
          (q ∈ U ↔ ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
            p ∈ linearSubspace k V W ∧ q ∈ linearSubspace k V W ∧
            Disjoint (linearSubspace k V W) (B : Set (projectiveSpaceOfModule k V))) := by
  refine ⟨exists_line_disjoint_of_codimension_ge_two k V B hcodim p hp hpB, ?_⟩
  have hSclosed := isClosed_image_projection_pointSubmodule k V B hcodim p hp hpB
  obtain ⟨y, hyc, hyS⟩ := exists_closedPoint_projection_notMem_image k V B hcodim p hp hpB
  refine ⟨(projectionDomain k V (pointSubmodule k V p)).ι.base ''
    ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹'
          (B : Set (projectiveSpaceOfModule k V))))ᶜ),
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isOpenMap _
      (hSclosed.isOpen_compl.preimage (by fun_prop)), ⟨y.val, ⟨y, hyS, rfl⟩, hyc⟩, ?_⟩
  rintro q hqc hqp
  constructor
  · rintro ⟨z, hzS, rfl⟩
    obtain ⟨h2, hpL, hqL, hdisj⟩ := lineSubmodule_spec k V B p hp hpB z hqc fun w hwB heq =>
      hzS ⟨w, hwB, heq⟩
    exact ⟨lineSubmodule k V p z.val, h2, hpL, hqL, hdisj⟩
  · rintro ⟨W, -, hpW, hqW, hdisj⟩
    have hqD : q ∈ ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
      rwa [coe_mapDomain_pointSubmodule k V p hp]
    refine ⟨⟨q, hqD⟩, fun hmem => ?_, rfl⟩
    obtain ⟨w, hwB, hw⟩ := hmem
    have hle : W ≤ pointSubmodule k V p ⊓ pointSubmodule k V q :=
      le_inf ((mem_linearSubspace_iff k V W p).mp hpW) ((mem_linearSubspace_iff k V W q).mp hqW)
    exact Set.disjoint_left.mp hdisj (linearSubspace_antitone k V hle
      (mem_linearSubspace_inf_of_projection_eq k V (pointSubmodule k V p) w ⟨q, hqD⟩ hw)) hwB

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
