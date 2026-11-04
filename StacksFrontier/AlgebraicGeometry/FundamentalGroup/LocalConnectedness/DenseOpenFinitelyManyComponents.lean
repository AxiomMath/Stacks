module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.SpreadingOutFinitePresentation

/-!
# Finite étale covers across a dense open with finitely many local components

Let `U` be a dense open subscheme of a scheme `X`.  Assume that every quasi-compact open of `X`
has only finitely many irreducible components, and that for every point `x` of `X` outside `U`
the punctured spectrum of a strict henselization of the local ring `𝒪_{X, x}` is connected.
Then base change of finite étale covers along `U ⟶ X` is fully faithful: a morphism between the
restrictions to `U` of two finite étale covers of `X` comes from a unique morphism over `X`.

Faithfulness holds because a dense open inclusion is dominant.  For fullness, a morphism of
restricted covers is a section over `U` of the finite étale internal Hom scheme, so it suffices
to extend a section of a finite étale cover of `X` from `U` to the whole of `X`.  The opens
carrying an extension of a given section are closed under unions — density forces any two
extensions to agree on their overlap — so there is a largest such open `M`.  If `M` were not
everything, the generic point `x` of an irreducible component of `X ∖ M` would be a point at
which the preimage of `M` in `Spec 𝒪_{X, x}` is exactly the punctured spectrum; the section then
extends over `Spec 𝒪_{X, x}`, spreads out to an open neighbourhood of `x`, and — after shrinking
that neighbourhood — agrees with the section on `M` over the overlap.  Glueing the two would
enlarge `M`, a contradiction.

The finiteness hypothesis on irreducible components enters exactly at the shrinking step: it
makes the closure of an open set the set of specializations of its points, so a point not in the
image of the disagreement locus is not in the closure of that image either, and cutting the
neighbourhood down by the complement of that closure removes all disagreement.

## Main results

* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents` —
  **Stacks Tag 0BQG**, full faithfulness of base change of finite étale covers to a dense open.

## Implementation notes

Finite étale covers are `AlgebraicGeometry.FiniteEtaleOver` and base change is
`AlgebraicGeometry.finiteEtaleBaseChange`.  The local hypothesis at a point outside the dense
open is `AlgebraicGeometry.IsConnectedPuncturedStrictHenselization`, quantified over every strict
henselization of the local ring in the sense of
`Stacks.StrictHenselization.IsStrictHenselization`; this avoids choosing a strict henselization,
and one exists, so the hypothesis is never vacuous.

Extensions of a section are carried as honest morphisms `V.toScheme ⟶ Y` into the source of a
finite étale morphism `Y ⟶ X`, rather than as morphisms of covers; the passage between the two
presentations happens once, in the main theorem itself, through the finite étale internal Hom
scheme.  A section over an open is turned into a section over the whole base by fullness of base
change applied to the trivial cover.

## References

* [Stacks Project, Tag 0BQG](https://stacks.math.columbia.edu/tag/0BQG)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 0BX6](https://stacks.math.columbia.edu/tag/0BX6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open IsLocalRing
open Stacks.Divisors

namespace AlgebraicGeometry

/-! ### Sections of a finite étale cover -/

/-- The trivial finite étale cover of a scheme by itself. -/
private def idFiniteEtaleOver (S : Scheme.{u}) : FiniteEtaleOver S :=
  MorphismProperty.Over.mk ⊤ (𝟙 S) (MorphismProperty.id_mem _ S)

/-- **Sections extend when base change to an open is full.** If base change of finite étale
covers along the inclusion of an open `U` of `S` is a full functor, then every section over `U`
of a finite étale morphism `p : Y ⟶ S` is the restriction of a section over `S`.

A section over `U` is exactly a morphism from the base change of the trivial cover to the base
change of `p`; fullness lifts it to a morphism of covers over `S`, whose underlying map is a
section of `p`. -/
private theorem exists_section_of_full_finiteEtaleBaseChange
    {S : Scheme.{u}} (U : S.Opens) (hfull : (finiteEtaleBaseChange U.ι).Full)
    {Y : Scheme.{u}} (p : Y ⟶ S) [IsFinite p] [Etale p]
    (s : U.toScheme ⟶ Y) (hs : s ≫ p = U.ι) :
    ∃ t : S ⟶ Y, t ≫ p = 𝟙 S ∧ U.ι ≫ t = s := by
  let F := finiteEtaleBaseChange U.ι
  let Yc : FiniteEtaleOver S := MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩
  let φl : pullback (𝟙 S) U.ι ⟶ pullback p U.ι :=
    pullback.lift (pullback.snd (𝟙 S) U.ι ≫ s) (pullback.snd (𝟙 S) U.ι)
      (by rw [Category.assoc, hs])
  have hφsnd : φl ≫ pullback.snd p U.ι = pullback.snd (𝟙 S) U.ι := pullback.lift_snd _ _ _
  have hφfst : φl ≫ pullback.fst p U.ι = pullback.snd (𝟙 S) U.ι ≫ s :=
    pullback.lift_fst _ _ _
  let φ : F.obj (idFiniteEtaleOver S) ⟶ F.obj Yc := MorphismProperty.Over.homMk φl hφsnd
  obtain ⟨g, hg⟩ := hfull.map_surjective φ
  have hgfst : (F.map g).left ≫ pullback.fst p U.ι = pullback.fst (𝟙 S) U.ι ≫ g.left :=
    finiteEtaleBaseChange_map_left_fst U.ι g
  have hgl : (F.map g).left = φl := congrArg (fun q => q.left) hg
  have key : pullback.snd (𝟙 S) U.ι ≫ s = pullback.fst (𝟙 S) U.ι ≫ g.left := by
    rw [← hφfst, ← hgl]
    exact hgfst
  have hfsteq : pullback.fst (𝟙 S) U.ι = pullback.snd (𝟙 S) U.ι ≫ U.ι :=
    (Category.comp_id _).symm.trans pullback.condition
  have hiso : IsIso (pullback.snd (𝟙 S) U.ι) :=
    (IsPullback.of_hasPullback (𝟙 S) U.ι).isIso_snd_of_isIso
  refine ⟨g.left, MorphismProperty.Over.w g, ?_⟩
  apply (cancel_epi (pullback.snd (𝟙 S) U.ι)).mp
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (fun q ↦ q ≫ g.left) hfsteq.symm).trans key.symm

/-- **A section extends over the local scheme at a point where the open is the puncture.** Let
`p : Y ⟶ X` be finite étale, let `U` be an open of `X` and let `x` be a point whose local scheme
meets `U` exactly in the punctured spectrum of `𝒪_{X, x}`.  If the punctured spectrum of every
strict henselization of `𝒪_{X, x}` is connected, then a section of `p` over `U` extends to a
section over `Spec 𝒪_{X, x}`, compatibly over the preimage of `U`.

The extension is produced by full faithfulness of base change to a punctured spectrum, Stacks
0BLQ, applied to the base change of `p` to `Spec 𝒪_{X, x}`. -/
private theorem extend_section_to_stalk
    {X : Scheme.{u}} (U : X.Opens) (x : X)
    (hpunct : (X.fromSpecStalk x) ⁻¹ᵁ U = puncturedSpectrum (X.presheaf.stalk x))
    (hconn : IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
    (s : U.toScheme ⟶ Y) (hs : s ≫ p = U.ι) :
    ∃ t : Spec (X.presheaf.stalk x) ⟶ Y,
      t ≫ p = X.fromSpecStalk x ∧
      ((X.fromSpecStalk x) ⁻¹ᵁ U).ι ≫ t = ((X.fromSpecStalk x) ∣_ U) ≫ s := by
  obtain ⟨ff⟩ : Nonempty
      (finiteEtaleBaseChange (((X.fromSpecStalk x) ⁻¹ᵁ U).ι)).FullyFaithful := by
    rw [hpunct]
    exact nonempty_fullyFaithful_puncturedSpectrum_of_connected (X.presheaf.stalk x) hconn
  have hpb : finiteEtale (pullback.snd p (X.fromSpecStalk x)) :=
    MorphismProperty.pullback_snd p (X.fromSpecStalk x) ⟨inferInstance, inferInstance⟩
  have : IsFinite (pullback.snd p (X.fromSpecStalk x)) := hpb.1
  have : Etale (pullback.snd p (X.fromSpecStalk x)) := hpb.2
  have hcond : (((X.fromSpecStalk x) ∣_ U) ≫ s) ≫ p =
      ((X.fromSpecStalk x) ⁻¹ᵁ U).ι ≫ X.fromSpecStalk x := by
    rw [Category.assoc, hs]
    exact morphismRestrict_ι (X.fromSpecStalk x) U
  let sV : ((X.fromSpecStalk x) ⁻¹ᵁ U).toScheme ⟶ pullback p (X.fromSpecStalk x) :=
    pullback.lift (((X.fromSpecStalk x) ∣_ U) ≫ s) ((X.fromSpecStalk x) ⁻¹ᵁ U).ι hcond
  have hsV : sV ≫ pullback.snd p (X.fromSpecStalk x) =
      ((X.fromSpecStalk x) ⁻¹ᵁ U).ι := pullback.lift_snd _ _ _
  obtain ⟨t, ht, hst⟩ := exists_section_of_full_finiteEtaleBaseChange
    ((X.fromSpecStalk x) ⁻¹ᵁ U) ff.full (pullback.snd p (X.fromSpecStalk x)) sV hsV
  refine ⟨t ≫ pullback.fst p (X.fromSpecStalk x), ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  · rw [← Category.assoc, hst]
    exact pullback.lift_fst _ _ _

/-! ### Closures of opens on a space with finitely many irreducible components -/

/-- On a sober space with finitely many irreducible components, a point in the closure of an open
set is a specialization of a point of that set.

The generic points of the irreducible components are finite in number and dense, so the open set
is contained in the closure of the finitely many generic points it contains, and the closure of a
finite set is the union of the closures of its points. -/
private theorem exists_specializes_of_mem_closure_isOpen
    {T : Type*} [TopologicalSpace T] [T0Space T] [QuasiSober T]
    (hfin : (irreducibleComponents T).Finite)
    {V : Set T} (hV : IsOpen V) {x : T} (hx : x ∈ closure V) :
    ∃ y ∈ V, y ⤳ x := by
  have hd : Dense (genericPoints T) := by
    rw [dense_iff_closure_eq, genericPoints.closure]
  have hsub : V ⊆ closure (genericPoints T ∩ V) := by
    simpa [Set.inter_comm] using hd.open_subset_closure_inter hV
  have hx' : x ∈ closure (genericPoints T ∩ V) :=
    closure_minimal hsub isClosed_closure hx
  have heq : genericPoints T ∩ V = ⋃ y ∈ genericPoints T ∩ V, ({y} : Set T) :=
    (Set.biUnion_of_singleton _).symm
  rw [heq, ((genericPoints.finite hfin).inter_of_left V).closure_biUnion] at hx'
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx'
  exact ⟨y, hy.2, specializes_iff_mem_closure.mpr hxy⟩

/-- On a scheme whose quasi-compact opens have finitely many irreducible components, a point in
the closure of an open set is a specialization of a point of that set.  The question is local, so
it reduces to an affine open neighbourhood of the point, which is quasi-compact and sober. -/
private theorem exists_specializes_of_mem_closure_isOpen_scheme
    (X : Scheme.{u})
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {D : Set X} (hD : IsOpen D) {x : X} (hx : x ∈ closure D) :
    ∃ y ∈ D, y ⤳ x := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : X.Opens)) (x := x) trivial
  have : QuasiSober V := V.isOpenEmbedding'.quasiSober
  have hx' : (⟨x, hxV⟩ : V) ∈ closure (Subtype.val ⁻¹' D) := by
    rw [← V.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
    exact hx
  obtain ⟨y, hy, hspec⟩ := exists_specializes_of_mem_closure_isOpen
    (hfinite V hV.isCompact) (hD.preimage continuous_subtype_val) hx'
  exact ⟨y.val, hy, hspec.map continuous_subtype_val⟩

/-! ### Shrinking a neighbourhood until two sections agree -/

/-- The locus of the overlap of two opens where two sections of a separated étale morphism agree
is closed: a morphism into the overlap lands in it exactly when the sections agree after it. It
is the image of the equalizer of the two induced maps of `X`-schemes. -/
private theorem exists_isClosed_agreementLocus
    {X Y : Scheme.{u}} (p : Y ⟶ X) [IsSeparated p] [Etale p]
    (U V : X.Opens) (s : U.toScheme ⟶ Y) (t : V.toScheme ⟶ Y)
    (hs : s ≫ p = U.ι) (ht : t ≫ p = V.ι) :
    ∃ S : Set ((pullback U.ι V.ι : Scheme.{u}) : Type u), IsClosed S ∧
      (∀ {T : Scheme.{u}} (j : T ⟶ pullback U.ι V.ι), Set.range j ⊆ S →
        j ≫ pullback.fst U.ι V.ι ≫ s = j ≫ pullback.snd U.ι V.ι ≫ t) ∧
      (∀ {T : Scheme.{u}} (a : T ⟶ pullback U.ι V.ι),
        a ≫ pullback.fst U.ι V.ι ≫ s = a ≫ pullback.snd U.ι V.ι ≫ t →
          Set.range a ⊆ S) := by
  let P := pullback U.ι V.ι
  let r : P ⟶ X := pullback.fst U.ι V.ι ≫ U.ι
  let Po : Over X := Over.mk r
  let Yo : Over X := Over.mk p
  let fo : Po ⟶ Yo := Over.homMk (pullback.fst U.ι V.ι ≫ s) (by
    change (pullback.fst U.ι V.ι ≫ s) ≫ p = pullback.fst U.ι V.ι ≫ U.ι
    rw [Category.assoc, hs])
  let go : Po ⟶ Yo := Over.homMk (pullback.snd U.ι V.ι ≫ t) (by
    change (pullback.snd U.ι V.ι ≫ t) ≫ p = pullback.fst U.ι V.ι ≫ U.ι
    rw [Category.assoc, ht]
    exact pullback.condition.symm)
  let e := (equalizer.ι fo go).left
  have : IsSeparated Yo.hom := inferInstanceAs (IsSeparated p)
  have : Etale Yo.hom := inferInstanceAs (Etale p)
  have : IsOpenImmersion e := isOpenImmersion_equalizer_ι_left fo go
  have hef : e ≫ pullback.fst U.ι V.ι ≫ s = e ≫ pullback.snd U.ι V.ι ≫ t :=
    congrArg (fun m ↦ m.left) (equalizer.condition fo go)
  refine ⟨Set.range e, (Scheme.Hom.isClosedEmbedding e).isClosed_range,
    fun j hj ↦ ?_, fun a ha ↦ ?_⟩
  · rw [← IsOpenImmersion.lift_fac e j hj]
    simp only [Category.assoc, hef]
  · let ao : Over.mk (a ≫ r) ⟶ Po := Over.homMk a rfl
    have hae : ao ≫ fo = ao ≫ go := by
      ext1
      exact ha
    rintro _ ⟨z, rfl⟩
    refine ⟨(equalizer.lift ao hae).left z, ?_⟩
    have h := congrArg (fun m ↦ m.left) (equalizer.lift_ι ao hae)
    exact congrArg (fun m : _ ⟶ P ↦ m z) h

/-- On a scheme whose quasi-compact opens have finitely many irreducible components, a point `x`
is not in the closure of the image under an open immersion `r` of the complement of a closed set
`S`, provided every point of the source specializing to `x` under `r` lies in `S`. -/
private theorem notMem_closure_image_compl_of_specializes {X P : Scheme.{u}}
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (r : P ⟶ X) [IsOpenImmersion r] {S : Set P} (hS : IsClosed S) {x : X}
    (hloc : ∀ z, r z ⤳ x → z ∈ S) : x ∉ closure (r '' Sᶜ) := by
  intro hx
  obtain ⟨_, ⟨z, hz, rfl⟩, hzx⟩ := exists_specializes_of_mem_closure_isOpen_scheme X hfinite
    (r.isOpenEmbedding.isOpenMap _ hS.isOpen_compl) hx
  exact hz (hloc z hzx)

/-- Two sections of a finite étale morphism which agree over the local scheme at a point `x`
agree on the overlap of their domains with a small enough open neighbourhood of `x`.

The locus in the overlap of the two domains where the sections agree is the equalizer of the two
induced maps of `X`-schemes; it is an open immersion with closed image because the target is
étale and separated over `X`.  The image in `X` of the complement of that locus is open and, by
finiteness of the irreducible components of quasi-compact opens, its closure consists of
specializations of its points.  The local scheme at `x` lands in the agreement locus, so `x` is
not in that closure, and the neighbourhood may be cut down by the closure's complement. -/
private theorem shrink_section_agreement
    {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U V : X.Opens) (x : X) (hxV : x ∈ V)
    (s : U.toScheme ⟶ Y) (t : V.toScheme ⟶ Y)
    (hs : s ≫ p = U.ι) (ht : t ≫ p = V.ι)
    (he : ((X.fromSpecStalk x) ⁻¹ᵁ U).ι ≫ V.fromSpecStalkOfMem x hxV ≫ t =
      ((X.fromSpecStalk x) ∣_ U) ≫ s) :
    ∃ (W : X.Opens) (_ : x ∈ W) (hWV : W ≤ V),
      pullback.fst U.ι W.ι ≫ s = pullback.snd U.ι W.ι ≫ X.homOfLE hWV ≫ t := by
  obtain ⟨S, hS, hSeq, hSsub⟩ := exists_isClosed_agreementLocus p U V s t hs ht
  let L := (X.fromSpecStalk x) ⁻¹ᵁ U
  let r : pullback U.ι V.ι ⟶ X := pullback.fst U.ι V.ι ≫ U.ι
  have hacond : ((X.fromSpecStalk x) ∣_ U) ≫ U.ι =
      (L.ι ≫ V.fromSpecStalkOfMem x hxV) ≫ V.ι := by
    rw [Category.assoc, V.fromSpecStalkOfMem_ι, morphismRestrict_ι]
  obtain ⟨a, hafst, hasnd⟩ := pullback.lift' _ _ hacond
  have har : a ≫ r = L.ι ≫ X.fromSpecStalk x := (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ U.ι) hafst).trans (morphismRestrict_ι (X.fromSpecStalk x) U))
  have hae : a ≫ pullback.fst U.ι V.ι ≫ s = a ≫ pullback.snd U.ι V.ι ≫ t := by
    rw [← Category.assoc, hafst, ← Category.assoc, hasnd, Category.assoc]
    exact he.symm
  have hxD : x ∉ closure (r '' Sᶜ) := notMem_closure_image_compl_of_specializes hfinite r hS
    fun z hzx ↦ by
      obtain ⟨q, hq⟩ : r z ∈ Set.range (X.fromSpecStalk x) := by rwa [Scheme.range_fromSpecStalk]
      have hqU : q ∈ L := by
        change X.fromSpecStalk x q ∈ U
        rw [hq]
        exact (pullback.fst U.ι V.ι z).property
      have haz : a ⟨q, hqU⟩ = z := by
        apply r.isEmbedding.injective
        change (a ≫ r) ⟨q, hqU⟩ = r z
        rw [har]
        exact hq
      exact haz ▸ hSsub a hae (Set.mem_range_self (⟨q, hqU⟩ : L.toScheme))
  let W : X.Opens := V ⊓ ⟨(closure (r '' Sᶜ))ᶜ, isClosed_closure.isOpen_compl⟩
  have hWV : W ≤ V := inf_le_left
  have hjcond : pullback.fst U.ι W.ι ≫ U.ι =
      (pullback.snd U.ι W.ι ≫ X.homOfLE hWV) ≫ V.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact pullback.condition
  obtain ⟨j, hjfst, hjsnd⟩ := pullback.lift' _ _ hjcond
  have hjr : j ≫ r = pullback.snd U.ι W.ι ≫ W.ι :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.ι) hjfst).trans pullback.condition)
  have hj : Set.range j ⊆ S := by
    rintro _ ⟨z, rfl⟩
    by_contra hz
    have hmem : (j ≫ r) z ∈ closure (r '' Sᶜ) := subset_closure ⟨j z, hz, rfl⟩
    apply (pullback.snd U.ι W.ι z).property.2
    rwa [hjr] at hmem
  have h := hSeq j hj
  rw [← Category.assoc, hjfst, ← Category.assoc, hjsnd, Category.assoc] at h
  exact ⟨W, ⟨hxV, hxD⟩, hWV, h⟩

/-- **A section extends across a point of the complement.** A section of a finite étale morphism
`p : Y ⟶ X` over an open `U` extends to an open neighbourhood of a point `x` whose local scheme
meets `U` exactly in the punctured spectrum, agreeing with the original section on the overlap.

The section first extends over `Spec 𝒪_{X, x}`, then spreads out to a section on some open
neighbourhood of `x` because `p` is locally of finite presentation (Stacks 0BX6), and finally
the neighbourhood is shrunk until the two sections agree on the overlap. -/
private theorem extend_section_near_point
    {X : Scheme.{u}} (U : X.Opens)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (x : X)
    (hpunct : (X.fromSpecStalk x) ⁻¹ᵁ U = puncturedSpectrum (X.presheaf.stalk x))
    (hconn : IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
    (s : U.toScheme ⟶ Y) (hs : s ≫ p = U.ι) :
    ∃ (W : X.Opens) (_ : x ∈ W) (w : W.toScheme ⟶ Y),
      w ≫ p = W.ι ∧
      pullback.fst U.ι W.ι ≫ s = pullback.snd U.ι W.ι ≫ w := by
  obtain ⟨t, ht, he⟩ := extend_section_to_stalk U x hpunct hconn p s hs
  obtain ⟨V, hxV, v, hv1, hv2⟩ :=
    spread_out_of_locallyOfFinitePresentation' (𝟙 X) p (x := x) t
      (by rwa [Category.comp_id])
  have hv : v ≫ p = V.ι := by rw [hv2, Category.comp_id]
  obtain ⟨W, hxW, hWV, hw⟩ :=
    shrink_section_agreement p hfinite U V x hxV s v hs hv (by rwa [← hv1])
  refine ⟨W, hxW, X.homOfLE hWV ≫ v, ?_, ?_⟩
  · rw [Category.assoc, hv, Scheme.homOfLE_ι]
  · simpa only [Category.assoc] using hw

/-! ### Glueing the extensions over a dense open -/

/-- Two extensions of a section from a dense open agree on the overlap of their domains: the two
induced maps on the overlap agree on the dense open, which is dominant there. -/
private theorem section_extensions_agree
    {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
    (U V W : X.Opens) (hU : Dense (U : Set X)) (hUV : U ≤ V) (hUW : U ≤ W)
    (s : U.toScheme ⟶ Y) (v : V.toScheme ⟶ Y) (w : W.toScheme ⟶ Y)
    (hv : v ≫ p = V.ι) (hw : w ≫ p = W.ι)
    (hsv : X.homOfLE hUV ≫ v = s) (hsw : X.homOfLE hUW ≫ w = s) :
    pullback.fst V.ι W.ι ≫ v = pullback.snd V.ι W.ι ≫ w := by
  have hjcond : X.homOfLE hUV ≫ V.ι = X.homOfLE hUW ≫ W.ι := by
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  obtain ⟨j, hjfst, hjsnd⟩ := pullback.lift' (X.homOfLE hUV) (X.homOfLE hUW) hjcond
  have hjr : j ≫ (pullback.fst V.ι W.ι ≫ V.ι) = U.ι := by
    rw [← Category.assoc, hjfst, Scheme.homOfLE_ι]
  have : IsDominant U.ι := Opens.isDominant_ι hU
  have : IsDominant (j ≫ (pullback.fst V.ι W.ι ≫ V.ι)) := by
    rw [hjr]
    infer_instance
  have : IsDominant j :=
    IsDominant.of_comp_of_isOpenImmersion j (pullback.fst V.ι W.ι ≫ V.ι)
  refine eq_of_isDominant_of_finiteEtale p ?_ j ?_
  · rw [Category.assoc, Category.assoc, hv, hw]
    exact pullback.condition
  · rw [reassoc_of% hjfst, reassoc_of% hjsnd, hsv, hsw]

/-- Sections of a morphism over a family of opens which agree on all pairwise overlaps glue to a
section over the union of the family. -/
private theorem glue_sections_iSup
    {X Y : Scheme.{u}} (p : Y ⟶ X) {I : Type*} (V : I → X.Opens)
    (v : ∀ i, (V i).toScheme ⟶ Y) (hv : ∀ i, v i ≫ p = (V i).ι)
    (hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ v i =
      pullback.snd (V i).ι (V j).ι ≫ v j) :
    ∃ t : (⨆ i, V i).toScheme ⟶ Y, t ≫ p = (⨆ i, V i).ι ∧
      ∀ i, X.homOfLE (le_iSup V i) ≫ t = v i := by
  let C := Scheme.Opens.iSupOpenCover V
  have hCι : ∀ i, C.f i ≫ (⨆ i, V i).ι = (V i).ι := fun i ↦
    Scheme.homOfLE_ι X (le_iSup V i)
  have hc' : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ v i =
      pullback.snd (C.f i) (C.f j) ≫ v j := by
    intro i j
    have hab : pullback.fst (C.f i) (C.f j) ≫ (V i).ι =
        pullback.snd (C.f i) (C.f j) ≫ (V j).ι := by
      rw [← hCι i, ← hCι j, ← Category.assoc, ← Category.assoc, pullback.condition]
    obtain ⟨k, hkfst, hksnd⟩ := pullback.lift'
      (pullback.fst (C.f i) (C.f j)) (pullback.snd (C.f i) (C.f j)) hab
    calc pullback.fst (C.f i) (C.f j) ≫ v i
        = (k ≫ pullback.fst (V i).ι (V j).ι) ≫ v i :=
          congrArg (fun q ↦ q ≫ v i) hkfst.symm
      _ = k ≫ pullback.fst (V i).ι (V j).ι ≫ v i := Category.assoc _ _ _
      _ = k ≫ pullback.snd (V i).ι (V j).ι ≫ v j := congrArg (fun q ↦ k ≫ q) (hc i j)
      _ = (k ≫ pullback.snd (V i).ι (V j).ι) ≫ v j := (Category.assoc _ _ _).symm
      _ = pullback.snd (C.f i) (C.f j) ≫ v j := congrArg (fun q ↦ q ≫ v j) hksnd
  refine ⟨C.glueMorphisms v hc', C.hom_ext _ _ fun i ↦ ?_,
    fun i ↦ C.ι_glueMorphisms v hc' i⟩
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ p) (C.ι_glueMorphisms v hc' i)).trans ((hv i).trans (hCι i).symm)

/-- Two sections of a morphism which agree on the intersection of their domains glue to a section
over the union. -/
private theorem glue_sections_sup
    {X Y : Scheme.{u}} (p : Y ⟶ X) (V W : X.Opens)
    (v : V.toScheme ⟶ Y) (w : W.toScheme ⟶ Y)
    (hv : v ≫ p = V.ι) (hw : w ≫ p = W.ι)
    (hc : pullback.fst V.ι W.ι ≫ v = pullback.snd V.ι W.ι ≫ w) :
    ∃ t : (V ⊔ W).toScheme ⟶ Y, t ≫ p = (V ⊔ W).ι ∧
      X.homOfLE le_sup_left ≫ t = v ∧ X.homOfLE le_sup_right ≫ t = w := by
  let D : Bool → X.Opens := fun b ↦ if b then W else V
  let d : ∀ b, (D b).toScheme ⟶ Y := fun b ↦ by
    cases b
    · exact v
    · exact w
  have hd : ∀ b, d b ≫ p = (D b).ι := by rintro (_ | _) <;> assumption
  have hdiag : ∀ (A : X.Opens) (a : A.toScheme ⟶ Y),
      pullback.fst A.ι A.ι ≫ a = pullback.snd A.ι A.ι ≫ a := fun A a ↦
    congrArg (· ≫ a) ((cancel_mono A.ι).mp (pullback.condition (f := A.ι) (g := A.ι)))
  have hcc : ∀ i j, pullback.fst (D i).ι (D j).ι ≫ d i =
      pullback.snd (D i).ι (D j).ι ≫ d j := by
    rintro (_ | _) (_ | _)
    · exact hdiag V v
    · exact hc
    · have h := congrArg (fun q ↦ (pullbackSymmetry W.ι V.ι).hom ≫ q) hc
      change pullback.fst W.ι V.ι ≫ w = pullback.snd W.ι V.ι ≫ v
      simpa using h.symm
    · exact hdiag W w
  obtain ⟨t, ht, hdt⟩ := glue_sections_iSup p D d hd hcc
  have hD : (⨆ b, D b) = V ⊔ W := by simp [D, iSup_bool_eq, sup_comm]
  have h0 := hdt false
  have h1 := hdt true
  dsimp only [D, d] at h0 h1
  refine ⟨X.homOfLE hD.symm.le ≫ t, ?_, ?_, ?_⟩
  · rw [Category.assoc, ht, Scheme.homOfLE_ι]
  · rwa [Scheme.homOfLE_homOfLE_assoc]
  · rwa [Scheme.homOfLE_homOfLE_assoc]

/-- **Sections of a finite étale morphism extend across a dense open.** Under the hypotheses that
quasi-compact opens of `X` have finitely many irreducible components and that the punctured
spectra of the strict henselizations at the points outside the dense open `U` are connected, a
section of a finite étale `p : Y ⟶ X` over `U` is the restriction of a section over `X`.

Density makes any two extensions of the section agree on their overlap, so the opens carrying an
extension are closed under arbitrary unions and there is a largest one, `M`.  Were `M` not all of
`X`, extending across the generic point of an irreducible component of `X ∖ M` and glueing would
produce a strictly larger one. -/
private theorem extend_section_from_dense_open
    (X : Scheme.{u}) (U : X.Opens)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (hU : Dense (U : Set X))
    (hconn : ∀ x : X, x ∉ U → IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p]
    (s : U.toScheme ⟶ Y) (hs : s ≫ p = U.ι) :
    ∃ t : X ⟶ Y, t ≫ p = 𝟙 X ∧ U.ι ≫ t = s := by
  classical
  let E : Set X.Opens := {V | ∃ (h : U ≤ V) (v : V.toScheme ⟶ Y),
    v ≫ p = V.ι ∧ X.homOfLE h ≫ v = s}
  have hUE : U ∈ E := ⟨le_rfl, s, hs, by rw [Scheme.homOfLE_rfl, Category.id_comp]⟩
  choose hUV v hv hvs using fun i : E ↦ i.property
  let V : E → X.Opens := fun i ↦ i.val
  let M : X.Opens := ⨆ i, V i
  have hUM : U ≤ M := le_iSup V ⟨U, hUE⟩
  have hc : ∀ i j, pullback.fst (V i).ι (V j).ι ≫ v i =
      pullback.snd (V i).ι (V j).ι ≫ v j := fun i j ↦
    section_extensions_agree p U (V i) (V j) hU (hUV i) (hUV j) s (v i) (v j)
      (hv i) (hv j) (hvs i) (hvs j)
  obtain ⟨t, ht, hvt⟩ := glue_sections_iSup p V v hv hc
  have hst : X.homOfLE hUM ≫ t = s := by
    have h2 : X.homOfLE (hUV ⟨U, hUE⟩) ≫ v ⟨U, hUE⟩ = s := hvs ⟨U, hUE⟩
    rw [Scheme.homOfLE_rfl, Category.id_comp] at h2
    exact (hvt ⟨U, hUE⟩).trans h2
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨x, hx, hpunct⟩ := exists_point_with_punctured_local_open X M hne
    obtain ⟨W, hxW, w, hw, htw⟩ := extend_section_near_point M hfinite x hpunct
      (hconn x fun h ↦ hx (hUM h)) p t ht
    obtain ⟨t', ht', htt', _⟩ := glue_sections_sup p M W t w ht hw htw
    have hmem : M ⊔ W ∈ E := by
      refine ⟨hUM.trans le_sup_left, t', ht', ?_⟩
      rw [← Scheme.homOfLE_homOfLE X hUM le_sup_left, Category.assoc, htt', hst]
    exact hx ((le_iSup V ⟨M ⊔ W, hmem⟩) (Or.inr hxW))
  have hiso : IsIso M.ι := by
    rw [hMtop]
    exact X.topIso.isIso_hom
  refine ⟨inv M.ι ≫ t, ?_, ?_⟩
  · rw [Category.assoc, ht, IsIso.inv_hom_id]
  · rw [← Scheme.homOfLE_ι X hUM, Category.assoc, IsIso.hom_inv_id_assoc, hst]

/-! ### The theorem -/

/-- If every section over an open `U` of a finite étale morphism to `X` extends to a section over
`X`, then every morphism `Yo ⨯ U ⟶ Zo` of finite étale `X`-schemes factors through the projection
to `Yo`.  The morphism is a section over `U` of the finite étale internal Hom scheme. -/
private theorem exists_lift_prod_of_forall_extend_section
    (X : Scheme.{u}) (U : X.Opens)
    (hext : ∀ {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] (s : U.toScheme ⟶ Y),
      s ≫ p = U.ι → ∃ t : X ⟶ Y, t ≫ p = 𝟙 X ∧ U.ι ≫ t = s)
    (Yo Zo : Over X) [IsFinite Yo.hom] [Etale Yo.hom] [IsFinite Zo.hom] [Etale Zo.hom]
    (mU : Yo ⨯ Over.mk U.ι ⟶ Zo) :
    ∃ g : Yo ⟶ Zo, (prod.fst : Yo ⨯ Over.mk U.ι ⟶ Yo) ≫ g = mU := by
  obtain ⟨W, hWfin, hWet, ⟨e⟩⟩ :=
    Stacks.FundamentalGroup.exists_finiteEtale_internalHom X Yo Zo
  have : IsFinite W.hom := hWfin
  have : Etale W.hom := hWet
  let B : Over X := Over.mk U.ι
  let T : Over X := Over.mk (𝟙 X)
  let i : B ⟶ T := Over.homMk U.ι
  let P := Yo ⨯ B
  let sB : B ⟶ W := (e.app (Opposite.op B)).inv mU
  obtain ⟨tW, htW, hUtW⟩ := hext W.hom sB.left sB.w
  let tB : T ⟶ W := Over.homMk tW htW
  let mT : Yo ⨯ T ⟶ Zo := (e.app (Opposite.op T)).hom tB
  let c : Yo ⟶ T := Over.homMk Yo.hom
  let η : Yo ⟶ Yo ⨯ T := prod.lift (𝟙 Yo) c
  let mapi : P ⟶ Yo ⨯ T := (prod.functor.obj Yo).map i
  have hm : mapi ≫ mT = mU := by
    have hn := congrArg (fun q => q tB) (e.hom.naturality i.op)
    change (e.app (Opposite.op B)).hom (i ≫ tB) = mapi ≫ mT at hn
    rw [show i ≫ tB = sB from Over.OverMorphism.ext hUtW] at hn
    have hmU : (e.app (Opposite.op B)).hom sB = mU := by
      simpa only [sB] using (e.app (Opposite.op B)).inv_hom_id_apply mU
    exact hn.symm.trans hmU
  have hci : (prod.fst (Y := B) : P ⟶ Yo) ≫ c = (prod.snd (X := Yo) : P ⟶ B) ≫ i := by
    ext1
    exact (prod.fst (Y := B)).w.trans (prod.snd (X := Yo)).w.symm
  have hmapη : mapi = (prod.fst (Y := B) : P ⟶ Yo) ≫ η := by
    change prod.map (𝟙 Yo) i = (prod.fst (Y := B) : P ⟶ Yo) ≫ η
    apply prod.hom_ext
    · simp only [prod.map_fst, Category.comp_id, η, prod.comp_lift, prod.lift_fst]
    · simp only [prod.map_snd, η, prod.comp_lift, prod.lift_snd]
      exact hci.symm
  refine ⟨η ≫ mT, ?_⟩
  change (prod.fst (Y := B) : P ⟶ Yo) ≫ η ≫ mT = mU
  rw [← Category.assoc, ← hmapη]
  exact hm

/-- If every section over an open `U` of a finite étale morphism to `X` extends to a section over
`X`, then base change of finite étale covers along `U ⟶ X` is full. -/
private theorem full_finiteEtaleBaseChange_of_forall_extend_section
    (X : Scheme.{u}) (U : X.Opens)
    (hext : ∀ {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] (s : U.toScheme ⟶ Y),
      s ≫ p = U.ι → ∃ t : X ⟶ Y, t ≫ p = 𝟙 X ∧ U.ι ≫ t = s) :
    (finiteEtaleBaseChange U.ι).Full := by
  let F := finiteEtaleBaseChange U.ι
  refine ⟨?_⟩
  intro Y Z h
  let Yo : Over X := Over.mk Y.hom
  let Zo : Over X := Over.mk Z.hom
  have : IsFinite Yo.hom := Y.prop.1
  have : Etale Yo.hom := Y.prop.2
  have : IsFinite Zo.hom := Z.prop.1
  have : Etale Zo.hom := Z.prop.2
  let B : Over X := Over.mk U.ι
  let P := Yo ⨯ B
  let θ : P.left ⟶ pullback Y.hom U.ι := (Over.prodLeftIsoPullback Yo B).hom
  have : IsIso θ := inferInstanceAs (IsIso (Over.prodLeftIsoPullback Yo B).hom)
  have hθfst : θ ≫ pullback.fst Y.hom U.ι = (prod.fst (Y := B)).left :=
    Over.prodLeftIsoPullback_hom_fst Yo B
  have hθsnd : θ ≫ pullback.snd Y.hom U.ι = (prod.snd (X := Yo)).left :=
    Over.prodLeftIsoPullback_hom_snd Yo B
  let hl : pullback Y.hom U.ι ⟶ pullback Z.hom U.ι := h.left
  have hh : hl ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
    MorphismProperty.Over.w h
  have hcondZ : pullback.fst Z.hom U.ι ≫ Zo.hom = pullback.snd Z.hom U.ι ≫ U.ι :=
    pullback.condition
  have hmUw : (θ ≫ hl ≫ pullback.fst Z.hom U.ι) ≫ Zo.hom = P.hom := by
    rw [Category.assoc, Category.assoc, hcondZ, ← Category.assoc hl, hh,
      ← Category.assoc, hθsnd]
    exact (prod.snd (X := Yo)).w
  obtain ⟨g, hmg⟩ := exists_lift_prod_of_forall_extend_section X U hext Yo Zo
    (Over.homMk (θ ≫ hl ≫ pullback.fst Z.hom U.ι) hmUw)
  let k : Y ⟶ Z := MorphismProperty.Over.homMk g.left g.w
  have hπ : pullback.fst Y.hom U.ι ≫ k.left = hl ≫ pullback.fst Z.hom U.ι := by
    rw [← cancel_epi θ, ← Category.assoc, hθfst]
    exact congrArg (fun q : P ⟶ Zo => q.left) hmg
  refine ⟨k, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (F.map k).left ≫ pullback.fst Z.hom U.ι = hl ≫ pullback.fst Z.hom U.ι
    rw [finiteEtaleBaseChange_map_left_fst]
    exact hπ
  · have hwk : (F.map k).left ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι :=
      MorphismProperty.Over.w (F.map k)
    change (F.map k).left ≫ pullback.snd Z.hom U.ι = hl ≫ pullback.snd Z.hom U.ι
    rw [hwk, hh]

/-- **Stacks Project, Tag 0BQG.** Let `U` be a dense open subscheme of a scheme `X` such that
every quasi-compact open of `X` has only finitely many irreducible components, and such that for
every point `x` of `X` outside `U` the punctured spectrum of every strict henselization of
`𝒪_{X, x}` is connected.  Then base change of finite étale covers along `U ⟶ X` is fully
faithful.

Faithfulness holds because a dense open inclusion is dominant (Stacks 0BQE).  For fullness, a
morphism between the restrictions to `U` of two covers `Y` and `Z` is a section over `U` of the
finite étale internal Hom scheme `Hom_X(Y, Z)`; that section extends to a section over `X`, which
is read back as a morphism of covers over `X`. -/
@[stacks 0BQG, sga "7 II 2.3.1" "partial"]
theorem fullyFaithful_finiteEtaleBaseChange_of_finite_irreducibleComponents
    (X : Scheme.{u}) (U : X.Opens)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (hU : Dense (U : Set X))
    (hconn : ∀ x : X, x ∉ U →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have : IsDominant U.ι := Opens.isDominant_ι hU
  have : (finiteEtaleBaseChange U.ι).Faithful :=
    faithful_finiteEtaleBaseChange_of_isDominant U.ι
  have : (finiteEtaleBaseChange U.ι).Full :=
    full_finiteEtaleBaseChange_of_forall_extend_section X U
      (@extend_section_from_dense_open X U hfinite hU hconn)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

end AlgebraicGeometry

end
