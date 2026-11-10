module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.FieldTheory.RatFuncIntDegree

/-!
# The Noetherian fppf site does not map to the big fppf site (Stacks 0GE9)

Let `S` be a scheme in a big fppf site. The locally Noetherian objects of the big fppf site
over `S` form a full subcategory which, endowed with those covering families of
`(Sch/S)_{fppf}` whose objects are again locally Noetherian, is the site
`(Noetherian/S)_{fppf}`, and the inclusion `u : (Noetherian/S)_{fppf} ⥤ (Sch/S)_{fppf}` is
continuous. **Stacks 0GE9** says that for `S = Spec 𝐅_p` the functor `u` nevertheless does not
define a morphism of sites: the induced functor `u_s` on sheaves of sets is not left exact.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.toBigFppfOver`: the inclusion `u`.
* `AlgebraicGeometry.LocallyNoetherianOver.IsCovering` and
  `AlgebraicGeometry.LocallyNoetherianOver.fppfTopology`: the covering families of
  `(Noetherian/S)_{fppf}` and the topology they generate.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.not_preservesMonomorphisms_toBigFppfOver`: the
  inclusion does not preserve monomorphisms.
* `AlgebraicGeometry.LocallyNoetherianOver.not_isMorphismOfSites_toBigFppfOver`:
  **Stacks 0GE9**.
* `AlgebraicGeometry.not_isLocallyNoetherian_pullback_perfectClosure`: the fibre product of
  `Spec K` with itself over `Spec k` is not locally Noetherian.
* `AlgebraicGeometry.exists_pullback_not_isLocallyNoetherian`: a fibre product of locally
  Noetherian schemes over a locally Noetherian base need not be locally Noetherian.

## The counterexample

Were `u` a morphism of sites, the pushforward `u^s` on sheaves of sets would have a left exact
left adjoint `u_s`. Both topologies are subcanonical — the big one because an fppf covering
family is a universal effective epimorphic family, the Noetherian one because `u` is fully
faithful and continuous — so `u_s` carries the Yoneda embedding of `(Noetherian/S)_{fppf}` to
the Yoneda embedding of `(Sch/S)_{fppf}` precomposed with `u`. A left exact functor preserves
monomorphisms and Yoneda reflects them, so `u` itself would preserve monomorphisms.

It does not. Take `k = 𝐅_p(t)` and let `K = ⋃_{n ≥ 0} k^{1/p^n}` be its perfect closure.

* `Spec K ⟶ Spec k` **is** a monomorphism of `(Noetherian/S)_{fppf}`: two morphisms from a
  locally Noetherian scheme to `Spec K` agreeing over `Spec k` are equal, because the nilradical
  of a Noetherian `𝐅_p`-algebra is nilpotent while every element of `K` has a `p`-power that
  lies in `k`, so the difference of the two induced ring maps is nilpotent of bounded order and
  is a `p^n`-th power.
* It is **not** a monomorphism of `(Sch/S)_{fppf}`: the two coprojections
  `K ⟶ K ⊗_k K` agree on `k`, and they are distinct because `k ⟶ K` is not surjective — the
  element `t` has no `p`-th root in `k`, as `intDegree` is multiplicative — so `k ⟶ K` is not an
  epimorphism of rings.

The second point is the source's contradiction, which exhibits the nontrivial `p`-torsion unit
`t^{1/p} ⊗ t^{-1/p}` of `K ⊗_k K`.

## Fibre products

The two points also show that the fibre product `Spec K ×_{Spec k} Spec K`, namely
`Spec (K ⊗_k K)`, is not locally Noetherian: it is the kernel pair of `Spec K ⟶ Spec k`, so
were it locally Noetherian its two projections to `Spec K` would agree by the first point,
making `Spec K ⟶ Spec k` a monomorphism of schemes against the second. Since `Spec K` and
`Spec k` are spectra of fields, the locally Noetherian objects of `(Sch/S)_{fppf}` are
therefore not closed under its fibre products.

## Implementation notes

The base scheme is `Spec (ULift (ZMod p))`, so that `Spec 𝐅_p` is a scheme in the ambient
universe; the base field of the counterexample is then `RatFunc (ULift (ZMod p))` and `K` is its
`PerfectClosure`, both of which are countable and hence small enough for any big fppf site.

The fibre product results are statements about schemes: the locally Noetherian objects are not
closed under the fibre products of the ambient site. That is strictly weaker than the assertion
that the site `(Noetherian/S)_τ` has no fibre products, which is about the full subcategory of
locally Noetherian objects itself; that assertion is
`AlgebraicGeometry.LocallyNoetherianOver.not_hasPullbacks`, and it needs a different diagram.

The gap between the two is not a technicality. A fibre product computed in a full subcategory
need not agree with the ambient one, and for the diagram `Spec K ⟶ Spec k ⟵ Spec K` above the
subcategory does have a fibre product: `Spec K ⟶ Spec k` is a monomorphism of
`(Noetherian/S)_{fppf}` by the first point, so `Spec K` with both projections the identity is
one, by `CategoryTheory.IsKernelPair.id_of_mono`, even though the ambient fibre product
`Spec (K ⊗_k K)` is not an object of the site at all. Refuting `HasPullbacks` for
`(Noetherian/S)_τ` therefore calls for a diagram whose fibre product functor on locally
Noetherian test objects is representable by no locally Noetherian object; the self-product of
`Spec k(u₀, u₁, u₂, …)` over `Spec k` is one, and the non-representability argument for it is
in `StacksFrontier.Examples.Sites.NoetherianSiteNoFibreProducts`.

## References

* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
* [Stacks Project, Tag 0GE2](https://stacks.math.columbia.edu/tag/0GE2)
* [Stacks Project, Tag 0GE9](https://stacks.math.columbia.edu/tag/0GE9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry

namespace LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the locally Noetherian objects of the big fppf site over `S` into that
site. -/
public abbrev toBigFppfOver : LocallyNoetherianOver B S hS ⥤ BigFppfOver B S hS :=
  ObjectProperty.ι (fun T : BigFppfOver B S hS =>
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))

/-- The underlying-scheme functor of the locally Noetherian site is the inclusion into the big
fppf site over `S` followed by the underlying-scheme functor of that site. -/
public theorem toBigFppfOver_comp_toScheme :
    toBigFppfOver B S hS ⋙ BigFppfOver.toScheme B S hS = toScheme B S hS :=
  rfl

/-- A family of locally Noetherian objects covers exactly when it covers in the big fppf site
over `S`. By Stacks 0GE1 (3) the sources of a covering family of a locally Noetherian object
are automatically locally Noetherian, so no further condition is needed. -/
public abbrev IsCovering (E : Covering (LocallyNoetherianOver B S hS)) : Prop :=
  BigFppfOver.IsCovering B S hS
    ⟨(toBigFppfOver B S hS).obj E.1, E.2.map (toBigFppfOver B S hS)⟩

/-- The precoverage presented by the covering families of locally Noetherian objects. -/
public def precoverage : Precoverage (LocallyNoetherianOver B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- Membership in the precoverage of the locally Noetherian site is characterized by a
presenting covering family. -/
public theorem mem_precoverage_iff {X : LocallyNoetherianOver B S hS}
    {R : Presieve X} :
    R ∈ precoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩ :=
  Iff.rfl

/-- **Stacks 0GE1 (4)** for the fppf topology: the topology on the locally Noetherian objects
of the big fppf site over `S` generated by the covering families of that site. -/
public abbrev fppfTopology : GrothendieckTopology (LocallyNoetherianOver B S hS) :=
  (precoverage B S hS).toGrothendieck

end LocallyNoetherianOver

/-- A functor defining a morphism of sites between subcanonical sites preserves
monomorphisms: its left exact left adjoint on sheaves identifies the two Yoneda embeddings, and
the Yoneda embedding of a subcanonical site is fully faithful into sheaves. -/
private lemma preservesMonomorphisms_of_isMorphismOfSites
    {sourceCategory : Type*} {targetCategory : Type*}
    [Category.{v} sourceCategory] [Category.{v} targetCategory]
    (inclusion : sourceCategory ⥤ targetCategory)
    (sourceTopology : GrothendieckTopology sourceCategory)
    (targetTopology : GrothendieckTopology targetCategory)
    [HasSheafify targetTopology (Type (v + 1))]
    [sourceTopology.Subcanonical] [targetTopology.Subcanonical]
    [∀ presheaf : sourceCategoryᵒᵖ ⥤ Type (v + 1),
      inclusion.op.HasLeftKanExtension presheaf]
    [h : IsMorphismOfSites.{v + 1} inclusion sourceTopology targetTopology] :
    inclusion.PreservesMonomorphisms := by
  obtain ⟨leftAdjoint, ⟨adjunction⟩, _⟩ := h.hasExactLeftAdjoint
  have := adjunction.isRightAdjoint
  let pullback := Functor.sheafPullbackConstruction.sheafPullback inclusion
    (Type (v + 1)) sourceTopology targetTopology
  have : PreservesFiniteLimits pullback :=
    preservesFiniteLimits_of_natIso
      (adjunction.leftAdjointUniq
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous inclusion
          (Type (v + 1)) sourceTopology targetTopology))
  let comparison : sourceTopology.uliftYoneda.{v + 1} ⋙ pullback ≅
      inclusion ⋙ uliftYoneda.{v + 1} ⋙ presheafToSheaf targetTopology (Type (v + 1)) :=
    (Functor.isoWhiskerRight sourceTopology.uliftYonedaCompSheafToPresheaf
      (inclusion.op.lan ⋙ presheafToSheaf targetTopology (Type (v + 1)))).trans
      ((Functor.associator _ _ _).symm.trans (Functor.isoWhiskerRight
        (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{v + 1} inclusion).symm
        (presheafToSheaf targetTopology (Type (v + 1)))))
  have : (inclusion ⋙ uliftYoneda.{v + 1} ⋙
      presheafToSheaf targetTopology (Type (v + 1))).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso comparison
  let comparison' : targetTopology.uliftYoneda.{v + 1} ≅ uliftYoneda.{v + 1} ⋙
      presheafToSheaf targetTopology (Type (v + 1)) :=
    (Functor.isoWhiskerLeft targetTopology.uliftYoneda.{v + 1}
      (sheafificationNatIso targetTopology (Type (v + 1)))).trans
      (Functor.isoWhiskerRight targetTopology.uliftYonedaCompSheafToPresheaf
        (presheafToSheaf targetTopology (Type (v + 1))))
  have : (inclusion ⋙ targetTopology.uliftYoneda.{v + 1}).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (Functor.isoWhiskerLeft inclusion comparison'.symm)
  exact ⟨fun morphism _ => targetTopology.uliftYoneda.{v + 1}.mono_of_mono_map
    ((inclusion ⋙ targetTopology.uliftYoneda.{v + 1}).map_mono morphism)⟩

/-- Two ring maps from a perfect field of characteristic `p` to a Noetherian ring of
characteristic `p` that agree on a `p`-radical subfield are equal: their difference is
nilpotent of order bounded by the nilpotency index of the nilradical, and every element of the
source is a `p^n`-th power. -/
private lemma ringHom_ext_of_perfect_of_noetherian
    {baseField perfectField targetRing : Type*}
    [Field baseField] [Field perfectField] [CommRing targetRing]
    (p : ℕ) [Fact p.Prime] [CharP perfectField p] [CharP targetRing p]
    [PerfectRing perfectField p] [IsNoetherianRing targetRing]
    (inclusion : baseField →+* perfectField) [IsPRadical inclusion p]
    (first second : perfectField →+* targetRing)
    (agreement : first.comp inclusion = second.comp inclusion) : first = second := by
  obtain ⟨exponent, hexponent⟩ := IsNoetherianRing.isNilpotent_nilradical targetRing
  have hheight : exponent ≤ p ^ exponent := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  ext element
  obtain ⟨root, hroot⟩ := (bijective_iterateFrobenius perfectField p exponent).surjective element
  have hnil : first root - second root ∈ nilradical targetRing := by
    obtain ⟨power, scalar, hscalar⟩ := IsPRadical.pow_mem inclusion p root
    refine mem_nilradical.mpr ⟨p ^ power, ?_⟩
    rw [sub_pow_char_pow, ← first.map_pow, ← second.map_pow, ← hscalar]
    exact sub_eq_zero.mpr (RingHom.congr_fun agreement scalar)
  have hzero : (first root - second root) ^ p ^ exponent = 0 := by
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hexponent]
    exact Ideal.pow_le_pow_right hheight (Ideal.pow_mem_pow hnil _)
  rw [sub_pow_char_pow, ← first.map_pow, ← second.map_pow] at hzero
  rw [iterateFrobenius_def] at hroot
  exact sub_eq_zero.mp (hroot ▸ hzero)

/-- Two morphisms from a locally Noetherian scheme to the spectrum of a perfect field of
characteristic `p` that agree after composing to the spectrum of a `p`-radical subfield are
equal. This is the previous ring-theoretic statement read on an affine cover. -/
private lemma hom_ext_to_perfectField_of_noetherian
    {baseField perfectField : Type u} [Field baseField] [Field perfectField]
    (p : ℕ) [Fact p.Prime] [CharP perfectField p] [PerfectRing perfectField p]
    (inclusion : baseField →+* perfectField) [IsPRadical inclusion p]
    {sourceScheme : Scheme.{u}} [IsLocallyNoetherian sourceScheme]
    (first second : sourceScheme ⟶ Spec (.of perfectField))
    (agreement : first ≫ Spec.map (CommRingCat.ofHom inclusion) =
      second ≫ Spec.map (CommRingCat.ofHom inclusion)) : first = second := by
  apply sourceScheme.affineCover.hom_ext
  intro index
  let affineScheme := sourceScheme.affineCover.X index
  let first' := affineScheme.isoSpec.inv ≫ sourceScheme.affineCover.f index ≫ first
  let second' := affineScheme.isoSpec.inv ≫ sourceScheme.affineCover.f index ≫ second
  have : IsLocallyNoetherian affineScheme := inferInstance
  have : IsLocallyNoetherian (Spec Γ(affineScheme, ⊤)) :=
    isLocallyNoetherian_of_isOpenImmersion affineScheme.isoSpec.inv
  have : IsNoetherianRing Γ(affineScheme, ⊤) := isLocallyNoetherian_Spec.mp this
  let firstRing := (Spec.preimage first').hom
  let secondRing := (Spec.preimage second').hom
  have hagree : firstRing.comp inclusion = secondRing.comp inclusion := by
    have hcomp : first' ≫ Spec.map (CommRingCat.ofHom inclusion) =
        second' ≫ Spec.map (CommRingCat.ofHom inclusion) := by
      simpa [first', second', Category.assoc] using congrArg (fun morphism =>
        affineScheme.isoSpec.inv ≫ sourceScheme.affineCover.f index ≫ morphism) agreement
    have h := congrArg Spec.preimage hcomp
    rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h
    exact congrArg CommRingCat.Hom.hom h
  have hequal : firstRing = secondRing := by
    rcases subsingleton_or_nontrivial Γ(affineScheme, ⊤) with _ | _
    · exact RingHom.ext fun _ => Subsingleton.elim _ _
    · have : CharP Γ(affineScheme, ⊤) p :=
        (firstRing.charP_iff_charP p).mp inferInstance
      exact ringHom_ext_of_perfect_of_noetherian p inclusion firstRing secondRing hagree
  have hequal' : first' = second' := by
    rw [← Spec.map_preimage first', ← Spec.map_preimage second']
    exact congrArg Spec.map (CommRingCat.hom_ext hequal)
  exact (cancel_epi affineScheme.isoSpec.inv).mp hequal'

/-- A field of rational functions in characteristic `p` is not perfect: its coordinate has no
`p`-th root, since the degree of a `p`-th power is divisible by `p`. Hence it is a proper
subfield of its perfect closure. -/
private lemma perfectClosure_of_ratFunc_not_surjective {field : Type*} [Field field]
    (p : ℕ) [Fact p.Prime] [CharP field p] :
    ¬ Function.Surjective (PerfectClosure.of (RatFunc field) p) := by
  intro hsurjective
  let root := (frobeniusEquiv (PerfectClosure (RatFunc field) p) p).symm
    (PerfectClosure.of (RatFunc field) p RatFunc.X)
  obtain ⟨element, helement⟩ := hsurjective root
  have hroot : root ^ p = PerfectClosure.of (RatFunc field) p RatFunc.X :=
    (frobeniusEquiv (PerfectClosure (RatFunc field) p) p).apply_symm_apply _
  have heq : element ^ p = (RatFunc.X : RatFunc field) := by
    apply (PerfectClosure.of (RatFunc field) p).injective
    rw [map_pow, helement, hroot]
  have hdegree := congrArg RatFunc.intDegree heq
  rw [Stacks.ratFunc_intDegree_pow, RatFunc.intDegree_X] at hdegree
  have hdivides : (p : ℤ) ∣ 1 := ⟨element.intDegree, hdegree.symm⟩
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdivides))

/-- The field of rational functions over a countable field is countable. -/
private lemma countable_ratFunc {field : Type*} [Field field] [Countable field] :
    Countable (RatFunc field) := by
  have : Countable (Polynomial field) := Polynomial.toFinsupp_injective.countable
  have hsurjective : Function.Surjective
      (fun pair : Polynomial field × Polynomial field =>
        (algebraMap (Polynomial field) (RatFunc field)) pair.1 /
          (algebraMap (Polynomial field) (RatFunc field)) pair.2) :=
    fun element => ⟨(element.num, element.denom), RatFunc.num_div_denom element⟩
  exact hsurjective.countable

namespace LocallyNoetherianOver

/-- **The inclusion of the locally Noetherian objects into the big fppf site over `Spec 𝐅_p`
does not preserve monomorphisms.** `Spec` of the perfect closure `K` of `𝐅_p(t)` is a
monomorphism over `Spec 𝐅_p(t)` in the locally Noetherian site, because a Noetherian
`𝐅_p`-algebra has nilpotent nilradical, whereas in the big fppf site it is not, because the two
coprojections `K ⟶ K ⊗_{𝐅_p(t)} K` are distinct. -/
public theorem not_preservesMonomorphisms_toBigFppfOver
    (p : ℕ) [Fact p.Prime] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (ULift.{u} (ZMod p))))) :
    ¬ (toBigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS).PreservesMonomorphisms := by
  classical
  intro hpreserves
  let := hpreserves
  let : Countable (ULift.{u} (ZMod p)) := Countable.of_equiv (ZMod p) Equiv.ulift.symm
  let baseField := RatFunc (ULift.{u} (ZMod p))
  let perfectField := PerfectClosure baseField p
  let inclusion := PerfectClosure.of baseField p
  let : Countable baseField := countable_ratFunc
  let : Countable perfectField := (PerfectClosure.mk_surjective baseField p).countable
  let : Algebra baseField perfectField := inclusion.toAlgebra
  have hcontains : ∀ (R : Type u) [CommRing R] [Countable R], B.Contains (Spec (.of R)) :=
    fun R _ _ => by
      change (Spec (.of R)).size < B.cutoff
      rw [Scheme.size_Spec]
      exact max_lt B.aleph0_lt_cutoff
        (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
  let baseMap := algebraMap (ULift.{u} (ZMod p)) baseField
  let perfectMap := inclusion.comp baseMap
  let baseObject : LocallyNoetherianOver B (Spec (.of (ULift.{u} (ZMod p)))) hS :=
    ⟨Over.mk (Y := B.obj (hcontains baseField)) (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom baseMap))), by
        change IsLocallyNoetherian (Spec (.of baseField))
        infer_instance⟩
  let perfectObject : LocallyNoetherianOver B (Spec (.of (ULift.{u} (ZMod p)))) hS :=
    ⟨Over.mk (Y := B.obj (hcontains perfectField)) (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom perfectMap))), by
        change IsLocallyNoetherian (Spec (.of perfectField))
        infer_instance⟩
  let morphism : perfectObject ⟶ baseObject := ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom inclusion))) (by
      apply ObjectProperty.hom_ext
      exact (Spec.map_comp (CommRingCat.ofHom baseMap)
        (CommRingCat.ofHom inclusion)).symm))
  have hmono : Mono morphism := by
    constructor
    intro testObject first second agreement
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    let : IsLocallyNoetherian testObject.obj.left.obj := testObject.property
    apply hom_ext_to_perfectField_of_noetherian p inclusion
    exact congrArg (fun map => map.hom.left.hom) agreement
  have hbigmono := (toBigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS).map_mono morphism
  change Mono morphism.hom at hbigmono
  let := hbigmono
  let tensorRing := perfectField ⊗[baseField] perfectField
  let : Countable tensorRing := by
    change Countable (Quotient (addConGen
      (TensorProduct.Eqv baseField perfectField perfectField)).toSetoid)
    infer_instance
  let firstRing : perfectField →+* tensorRing :=
    (Algebra.TensorProduct.includeLeft : perfectField →ₐ[baseField] tensorRing).toRingHom
  let secondRing : perfectField →+* tensorRing :=
    (Algebra.TensorProduct.includeRight : perfectField →ₐ[baseField] tensorRing).toRingHom
  let tensorMap := firstRing.comp perfectMap
  let tensorObject : BigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS :=
    Over.mk (Y := B.obj (hcontains tensorRing)) (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom tensorMap)))
  have hcoprojections : firstRing.comp inclusion = secondRing.comp inclusion := by
    ext element
    exact (Algebra.TensorProduct.includeLeft : perfectField →ₐ[baseField] tensorRing).commutes
      element |>.trans
      ((Algebra.TensorProduct.includeRight : perfectField →ₐ[baseField] tensorRing).commutes
        element).symm
  let first : tensorObject ⟶ perfectObject.obj :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom firstRing))) (by
      apply ObjectProperty.hom_ext
      exact (Spec.map_comp (CommRingCat.ofHom perfectMap)
        (CommRingCat.ofHom firstRing)).symm)
  let second : tensorObject ⟶ perfectObject.obj :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom secondRing))) (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom secondRing) ≫
        Spec.map (CommRingCat.ofHom perfectMap) =
        Spec.map (CommRingCat.ofHom tensorMap)
      rw [← Spec.map_comp]
      exact congrArg Spec.map
        (CommRingCat.hom_ext (congrArg (fun map => map.comp baseMap) hcoprojections.symm)))
  have hcomp : first ≫ morphism.hom = second ≫ morphism.hom := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom firstRing) ≫ Spec.map (CommRingCat.ofHom inclusion) =
      Spec.map (CommRingCat.ofHom secondRing) ≫ Spec.map (CommRingCat.ofHom inclusion)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hcoprojections)
  have hequal := (cancel_mono morphism.hom).mp hcomp
  have hring : firstRing = secondRing := by
    have hmaps : CommRingCat.ofHom firstRing = CommRingCat.ofHom secondRing :=
      Spec.map_injective (congrArg (fun map => map.left.hom) hequal)
    exact congrArg (fun map => map.hom) hmaps
  have : Algebra.IsEpi baseField perfectField :=
    (Algebra.isEpi_iff_forall_one_tmul_eq baseField perfectField).mpr
      (fun element => (RingHom.congr_fun hring element).symm)
  exact perfectClosure_of_ratFunc_not_surjective p
    (Algebra.IsEpi.surjective_algebraMap_of_field (k := baseField) (S := perfectField))

/-- **Stacks 0GE9.** *With `S = Spec 𝐅_p` the inclusion functor
`(Noetherian/S)_{fppf} ⟶ (Sch/S)_{fppf}` does not define a morphism of sites.*

Its pushforward on sheaves of sets has no left exact left adjoint. Both sites are subcanonical,
so a left exact `u_s` would identify the two Yoneda embeddings and force the inclusion to
preserve monomorphisms, which by
`AlgebraicGeometry.LocallyNoetherianOver.not_preservesMonomorphisms_toBigFppfOver` it does
not. -/
@[stacks 0GE9]
public theorem not_isMorphismOfSites_toBigFppfOver
    (p : ℕ) [Fact p.Prime] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (ULift.{u} (ZMod p))))) :
    ¬ IsMorphismOfSites.{u + 1}
      (toBigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (fppfTopology B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (BigFppfOver.topology B (Spec (.of (ULift.{u} (ZMod p)))) hS) := by
  intro _
  have : (fppfTopology B (Spec (.of (ULift.{u} (ZMod p)))) hS).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful
      (toBigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (fppfTopology B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (BigFppfOver.topology B (Spec (.of (ULift.{u} (ZMod p)))) hS)
  exact not_preservesMonomorphisms_toBigFppfOver p B hS
    (preservesMonomorphisms_of_isMorphismOfSites
      (toBigFppfOver B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (fppfTopology B (Spec (.of (ULift.{u} (ZMod p)))) hS)
      (BigFppfOver.topology B (Spec (.of (ULift.{u} (ZMod p)))) hS))

end LocallyNoetherianOver

/-- **The fibre product of `Spec K` with itself over `Spec k` is not locally Noetherian**, for
`k = 𝐅_p(t)` and `K` its perfect closure. A fibre product is the kernel pair of
`Spec K ⟶ Spec k`, and its two projections to `Spec K` agree over `Spec k`; were it locally
Noetherian they would therefore be equal, making `Spec K ⟶ Spec k` a monomorphism and hence
`k ⟶ K` an epimorphism of rings, which for a field source means surjective. It is not, the
coordinate `t` having no `p`-th root in `k`. -/
public theorem not_isLocallyNoetherian_pullback_perfectClosure (p : ℕ) [Fact p.Prime] :
    ¬ IsLocallyNoetherian (pullback
      (Spec.map (CommRingCat.ofHom (PerfectClosure.of (RatFunc (ULift.{u} (ZMod p))) p)))
      (Spec.map (CommRingCat.ofHom (PerfectClosure.of (RatFunc (ULift.{u} (ZMod p))) p)))) := by
  intro _
  let baseField := RatFunc (ULift.{u} (ZMod p))
  let perfectField := PerfectClosure baseField p
  let inclusion := PerfectClosure.of baseField p
  let : Algebra baseField perfectField := inclusion.toAlgebra
  have hmono : Mono (Spec.map (CommRingCat.ofHom inclusion)) :=
    IsKernelPair.mono_of_eq_fst_snd (IsPullback.of_hasPullback _ _)
      (hom_ext_to_perfectField_of_noetherian p inclusion _ _ pullback.condition)
  have hepi : Epi (CommRingCat.ofHom (algebraMap baseField perfectField)) :=
    ⟨fun first second agreement => by
      apply Spec.map_injective
      apply (cancel_mono (Spec.map (CommRingCat.ofHom inclusion))).mp
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map agreement⟩
  have : Algebra.IsEpi baseField perfectField := CommRingCat.epi_iff_epi.mp hepi
  exact perfectClosure_of_ratFunc_not_surjective p
    (Algebra.IsEpi.surjective_algebraMap_of_field (k := baseField) (S := perfectField))

/-- **A fibre product of locally Noetherian schemes over a locally Noetherian base need not be
locally Noetherian**: the locally Noetherian objects of a site of schemes are not closed under
its fibre products. The witness is `Spec K ⟶ Spec k ⟵ Spec K` with `k = 𝐅_2(t)` and `K` the
perfect closure of `k`.

This is a statement about schemes, and it is strictly weaker than the assertion that the site
`(Noetherian/S)_τ` has no fibre products: a fibre product computed inside the full subcategory
of locally Noetherian objects need not be the ambient one, and for this very diagram it exists,
namely `Spec K` with both projections the identity, as the implementation notes explain. It
therefore carries no `stacks` attribute. -/
public theorem exists_pullback_not_isLocallyNoetherian :
    ∃ (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S), IsLocallyNoetherian X ∧
      IsLocallyNoetherian Y ∧ IsLocallyNoetherian S ∧
      ¬ IsLocallyNoetherian (pullback f g) :=
  ⟨_, _, _, Spec.map (CommRingCat.ofHom (PerfectClosure.of (RatFunc (ULift.{u} (ZMod 2))) 2)),
    Spec.map (CommRingCat.ofHom (PerfectClosure.of (RatFunc (ULift.{u} (ZMod 2))) 2)),
    inferInstance, inferInstance, inferInstance,
    not_isLocallyNoetherian_pullback_perfectClosure 2⟩

end AlgebraicGeometry

add_to_stacks 0GE2 "the second assertion, for tau = fppf and S = Spec F_p: the example of \
Examples, Section 0GE8 that the remark defers to"
  AlgebraicGeometry.LocallyNoetherianOver.not_isMorphismOfSites_toBigFppfOver
