module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections

/-!
# Supported sections split along a clopen decomposition of the support

Let `F` be an abelian sheaf on the small étale site of a scheme `S` in a big étale site, let `W` be
an object of that site, and let `Z ⊆ W` be a locally closed subset written as a disjoint union
`Z = Z₁ ⊔ Z₂` of two locally closed subsets, each closed in `Z`. Then the group `H_Z(F)` of
sections supported on `Z` — Stacks 0F6F, implemented as sections over the canonical open
`coborder Z` whose support lies in `Z` — is the direct sum of `H_{Z₁}(F)` and `H_{Z₂}(F)`, the two
transition maps of Stacks 0F6H being the inclusions of the summands.

The proof is the separation of the two pieces by Zariski opens. Each of `Z₁` and `Z₂` is closed in
the canonical open `coborder Z` of `Z`, so it is cut out there by a closed subset of `W`; removing
the one that cuts out `Z₂` from `coborder Z` leaves an open `D₁` which contains `Z₁`, as a closed
subset, and misses `Z₂`, and symmetrically for `D₂`. The two opens cover `coborder Z` because `Z₁`
and `Z₂` are disjoint. A section supported on `Z` restricts on `D₁` to a section supported on `Z₁`
and on `D₂` to one supported on `Z₂`; these are the two components, and their sum agrees with the
original section on both `D₁` and `D₂`, hence everywhere. Conversely a section supported on `Z₁`
restricts to zero on `D₂` and vice versa, which is what makes the map injective: the two
components of an element of the kernel have supports inside the disjoint `Z₁` and `Z₂` and are
negatives of each other, so both have empty support.

Iterating the statement decomposes `H_Z(F)` along a finite clopen decomposition of `Z`, which is
how it is used: it is the sheaf-theoretic half of the injectivity argument for Stacks 0F6P, where
a support finite over an étale neighbourhood is split by Stacks 02LN into open-and-closed pieces
each containing a single point of the geometric fibre. Those pieces are *open* in the ambient
object, and on an open support the group of supported sections is simply the group of all sections
over it; that companion identification is recorded here too, since it is what turns a statement
about a piece of the decomposition into a statement about a section of `F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.supportOpenSdiff` — the canonical open of a locally closed subset
  with a closed subset removed. This is the open separating one piece of the decomposition from
  the other.
* `AlgebraicGeometry.SmallEtale.supportedSectionsClopenHom` — the map
  `H_{Z₁}(F) ⊕ H_{Z₂}(F) ⟶ H_{Z₁ ∪ Z₂}(F)`, the sum of the two transition maps of Stacks 0F6H.
* `AlgebraicGeometry.SmallEtale.supportedSectionsOpenEquivSections` — for an open support,
  the identification of `H_Z(F)` with the sections of `F` over `Z`.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_supportedSectionsClopenHom` and
  `AlgebraicGeometry.SmallEtale.supportedSectionsClopenEquiv` — that map is bijective, and the
  resulting isomorphism of abelian groups.
* `AlgebraicGeometry.SmallEtale.eq_zero_of_supportSection_eq_empty` and
  `AlgebraicGeometry.SmallEtale.eq_zero_of_map_openObjectHomOfLE_eq_zero` — a section with empty
  support vanishes, and a section vanishing on each of two Zariski opens covering its domain
  vanishes. These are the two uses made of Stacks 04FR part (1).
* `AlgebraicGeometry.SmallEtale.exists_isClosed_inter_supportOpen_eq` — a part of a locally closed
  subset which is closed in it is cut out on the canonical open by a closed subset of the ambient
  object. This is what produces the two separating opens.

## Implementation notes

Nothing here carries a Stacks tag. The statement is not one of the tags of the source: Stacks
performs this decomposition inline, inside the proof of Tag 0F6P, in the language of the
presentation of `f_{p!}F(V)` by generators `(Z, s)` and the relations 0F6K and 0F6L.

The two pieces are separated by *closed subsets of `W`* rather than by subsets of the canonical
open, so that all the opens in play are opens of the one object `W` and the transition maps are
all of the form `AlgebraicGeometry.SmallEtale.openObjectHomOfLE`. Consequently no identification
of an open of an open with an open of the ambient object is needed anywhere.

Both components are produced by `AlgebraicGeometry.SmallEtale.locallyClosedSupportEquiv` rather
than by `AlgebraicGeometry.SmallEtale.supportedSectionsOpenEquiv`, which is the same map: the
restriction description `AlgebraicGeometry.SmallEtale.locallyClosedSupportEquiv_restrict` is what
identifies the components, and it is stated for the former.

## References

* [Stacks Project, Tag 0F6F](https://stacks.math.columbia.edu/tag/0F6F)
* [Stacks Project, Tag 0F6H](https://stacks.math.columbia.edu/tag/0F6H)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- The inclusion of one Zariski open of an object of the small étale site into another is an
open immersion of schemes. -/
public instance isOpenImmersion_openObjectHomOfLE (W : SmallEtale B S hS)
    {V U : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U) :
    IsOpenImmersion ((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)) :=
  (openObjectHomOfLE_map B S hS W h) ▸ (inferInstance :
    IsOpenImmersion (((SmallEtale.toScheme B S hS).obj W).homOfLE h))

/-- The image of the inclusion of one Zariski open into another is the smaller one, seen inside
the larger. -/
public theorem opensRange_openObjectHomOfLE (W : SmallEtale B S hS)
    {V U : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U) :
    ((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)).opensRange =
      U.ι ⁻¹ᵁ V := by
  apply TopologicalSpace.Opens.ext
  change Set.range ((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)).base = _
  rw [openObjectHomOfLE_map B S hS W h]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    change (((SmallEtale.toScheme B S hS).obj W).homOfLE h y).1 ∈ V
    exact Set.mem_of_eq_of_mem (Scheme.homOfLE_apply h y) y.2
  · intro y hy
    exact ⟨⟨y.1, hy⟩, Subtype.ext (Scheme.homOfLE_apply h ⟨y.1, hy⟩)⟩

/-- The inclusion of one Zariski open into another does not move points. -/
public theorem val_base_openObjectHomOfLE (W : SmallEtale B S hS)
    {V U : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U)
    (z : ↥((SmallEtale.toScheme B S hS).obj (openObject B S hS W V))) :
    (((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)).base z).1 = z.1 := by
  rw [openObjectHomOfLE_map B S hS W h]
  exact Scheme.homOfLE_apply h z

/-- Pulling back along the inclusion of one Zariski open into another the trace on the larger
open of a subset of the ambient object gives its trace on the smaller open. -/
public theorem preimage_openObjectHomOfLE_preimage_ι (W : SmallEtale B S hS)
    {V U : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U)
    (T : Set ((SmallEtale.toScheme B S hS).obj W)) :
    ((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)).base ⁻¹'
        (U.ι.base ⁻¹' T) = V.ι.base ⁻¹' T := by
  ext z
  change (((SmallEtale.toScheme B S hS).map (openObjectHomOfLE B S hS W h)).base z).1 ∈ T ↔
    z.1 ∈ T
  rw [val_base_openObjectHomOfLE]

/-- A section whose maximal Zariski zero locus is everything is zero. -/
public theorem eq_zero_of_zeroOpen_eq_top (W : SmallEtale B S hS) (a : F.obj.obj (op W))
    (h : zeroOpen B S hS F W a = ⊤) : a = 0 := by
  have hz := (map_eq_zero_iff_le_zeroOpen B S hS F W a W (𝟙 W)).2 (h ▸ le_top)
  rwa [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hz

/-- A section with empty support is zero. -/
public theorem eq_zero_of_supportSection_eq_empty (W : SmallEtale B S hS)
    (a : F.obj.obj (op W)) (h : supportSection B S hS F W a = ∅) : a = 0 := by
  refine eq_zero_of_zeroOpen_eq_top B S hS F W a (TopologicalSpace.Opens.ext ?_)
  rw [TopologicalSpace.Opens.coe_top]
  exact Set.compl_empty_iff.mp h

/-- A section restricting to zero on each of two Zariski opens which cover its domain is zero. -/
public theorem eq_zero_of_map_openObjectHomOfLE_eq_zero (W : SmallEtale B S hS)
    {V₁ V₂ U : ((SmallEtale.toScheme B S hS).obj W).Opens} (h₁ : V₁ ≤ U) (h₂ : V₂ ≤ U)
    (hcover : U ≤ V₁ ⊔ V₂) (a : F.obj.obj (op (openObject B S hS W U)))
    (ha₁ : F.obj.map (openObjectHomOfLE B S hS W h₁).op a = 0)
    (ha₂ : F.obj.map (openObjectHomOfLE B S hS W h₂).op a = 0) : a = 0 := by
  have key : ∀ {V : ((SmallEtale.toScheme B S hS).obj W).Opens} (h : V ≤ U),
      F.obj.map (openObjectHomOfLE B S hS W h).op a = 0 → U.ι ⁻¹ᵁ V ≤ zeroOpen B S hS F _ a :=
    fun h ha => ((opensRange_openObjectHomOfLE B S hS W h).symm.le).trans
      ((map_eq_zero_iff_le_zeroOpen B S hS F _ a _ (openObjectHomOfLE B S hS W h)).1 ha)
  refine eq_zero_of_zeroOpen_eq_top B S hS F _ a (top_le_iff.mp fun z _ => ?_)
  rcases hcover z.2 with hz | hz
  · exact key h₁ ha₁ hz
  · exact key h₂ ha₂ hz

/-- A subset whose trace on a subspace is closed in that subspace has the same trace there as
some closed subset of the ambient space. -/
public theorem exists_isClosed_inter_eq_of_isClosed_preimage_val {X : Type*}
    [TopologicalSpace X] {A T : Set X} (h : IsClosed ((Subtype.val : A → X) ⁻¹' T)) :
    ∃ C : Set X, IsClosed C ∧ C ∩ A = T ∩ A := by
  obtain ⟨C, hC, hCeq⟩ := isClosed_induced_iff.1 h
  refine ⟨C, hC, ?_⟩
  rw [Set.inter_comm C, Set.inter_comm T]
  exact Subtype.preimage_coe_eq_preimage_coe_iff.1 hCeq

/-- A part of a locally closed subset which is closed in it is cut out on the canonical open of
that subset by a closed subset of the ambient object: the canonical open meets the closed subset
exactly in the part. -/
public theorem exists_isClosed_inter_supportOpen_eq (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    {T : Set ((SmallEtale.toScheme B S hS).obj W)} (hT : T ⊆ Z)
    (hcl : IsClosed ((Subtype.val : Z → _) ⁻¹' T)) :
    ∃ C : Set ((SmallEtale.toScheme B S hS).obj W), IsClosed C ∧
      C ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T := by
  obtain ⟨K, hK, hKeq⟩ := exists_isClosed_inter_eq_of_isClosed_preimage_val
    (isClosed_supportOpen_preimage B S hS W Z hZ)
  obtain ⟨C₀, hC₀, hC₀eq⟩ := exists_isClosed_inter_eq_of_isClosed_preimage_val hcl
  refine ⟨C₀ ∩ K, hC₀.inter hK, ?_⟩
  rw [Set.inter_assoc, hKeq, Set.inter_eq_self_of_subset_left (subset_supportOpen B S hS W Z hZ),
    hC₀eq, Set.inter_eq_self_of_subset_left hT]

/-- A section supported on `Z`, restricted to an open of the canonical open of `Z`, is supported
on the trace of `Z` on that open. -/
private theorem supportSection_restrict_subset_preimage_of_supported (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    {D : ((SmallEtale.toScheme B S hS).obj W).Opens} (hD : D ≤ supportOpen B S hS W Z hZ)
    (c : supportedSections B S hS F W Z hZ) :
    supportSection B S hS F (openObject B S hS W D)
        (F.obj.map (openObjectHomOfLE B S hS W hD).op c.val) ⊆ D.ι.base ⁻¹' Z := by
  refine (supportSection_restrict_subset_preimage B S hS F _ _
    (openObjectHomOfLE B S hS W hD) c.val).trans ?_
  refine (Set.preimage_mono c.property).trans ?_
  rw [preimage_openObjectHomOfLE_preimage_ι]

/-- The transition map of Stacks 0F6H along an inclusion of supports does not enlarge the
support: the image of a section supported on the smaller subset is still supported on it. -/
public theorem supportSection_supportedSectionsMap_subset (W : SmallEtale B S hS)
    (Z Z' : Set ((SmallEtale.toScheme B S hS).obj W))
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (h : Z ⊆ Z')
    (hc : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z))
    (a : supportedSections B S hS F W Z hZ) :
    supportSection B S hS F (openObject B S hS W (supportOpen B S hS W Z' hZ'))
        (supportedSectionsMap B S hS F W Z Z' hZ hZ' h hc a).val ⊆
      (supportOpen B S hS W Z' hZ').ι.base ⁻¹' Z := by
  rw [supportedSectionsMap_apply]
  exact supportSection_restrict_subset_preimage_of_supported B S hS F W hZ _ a

/-- A section supported on `Z` and represented on an open `D` of the canonical open of a larger
support is recovered, after the transition map to the larger support, by restricting back to `D`.
This is what identifies the components of the decomposition. -/
public theorem map_openObjectHomOfLE_supportedSectionsMap_val (W : SmallEtale B S hS)
    {Z Z' : Set ((SmallEtale.toScheme B S hS).obj W)}
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (hsub : Z ⊆ Z')
    (hcl : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z))
    {D : ((SmallEtale.toScheme B S hS).obj W).Opens}
    (hD : D ≤ supportOpen B S hS W Z' hZ')
    (hZD : Z ⊆ (D : Set ((SmallEtale.toScheme B S hS).obj W)))
    (hcD : IsClosed (D.ι.base ⁻¹' Z))
    (b : supportedSectionsOnOpen B S hS F W Z D) :
    F.obj.map (openObjectHomOfLE B S hS W hD).op
        (supportedSectionsMap B S hS F W Z Z' hZ hZ' hsub hcl
          ((locallyClosedSupportEquiv B S hS F W Z (supportOpen B S hS W Z hZ) D
            (subset_supportOpen B S hS W Z hZ) hZD
            (isClosed_supportOpen_preimage B S hS W Z hZ) hcD).symm b)).val = b.val := by
  set a := (locallyClosedSupportEquiv B S hS F W Z (supportOpen B S hS W Z hZ) D
    (subset_supportOpen B S hS W Z hZ) hZD
    (isClosed_supportOpen_preimage B S hS W Z hZ) hcD).symm b with ha
  have hant : supportOpen B S hS W Z' hZ' ≤ supportOpen B S hS W Z hZ :=
    supportOpen_antitone B S hS W Z Z' hZ hZ' hsub hcl
  have hstep : F.obj.map (openObjectHomOfLE B S hS W hD).op
        (F.obj.map (openObjectHomOfLE B S hS W hant).op a.val) =
      F.obj.map (openObjectHomOfLE B S hS W (hD.trans hant)).op a.val := by
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, openObjectHomOfLE_comp]
  refine Eq.trans (congrArg (F.obj.map (openObjectHomOfLE B S hS W hD).op)
    (supportedSectionsMap_apply B S hS F W Z Z' hZ hZ' hsub hcl a)) ?_
  refine hstep.trans ?_
  refine Eq.trans (locallyClosedSupportEquiv_restrict B S hS F W Z
    (supportOpen B S hS W Z hZ) D (subset_supportOpen B S hS W Z hZ) hZD
    (isClosed_supportOpen_preimage B S hS W Z hZ) hcD (hD.trans hant) a).symm ?_
  rw [ha, AddEquiv.apply_symm_apply]

/-- A section supported on `Z`, transported to a larger support, restricts to zero on any open of
the canonical open of that larger support which misses `Z`. -/
public theorem map_openObjectHomOfLE_supportedSectionsMap_eq_zero (W : SmallEtale B S hS)
    {Z Z' : Set ((SmallEtale.toScheme B S hS).obj W)}
    (hZ : IsLocallyClosed Z) (hZ' : IsLocallyClosed Z') (hsub : Z ⊆ Z')
    (hcl : IsClosed ((Subtype.val : Z' → _) ⁻¹' Z))
    {D : ((SmallEtale.toScheme B S hS).obj W).Opens}
    (hD : D ≤ supportOpen B S hS W Z' hZ')
    (hempty : (D : Set ((SmallEtale.toScheme B S hS).obj W)) ∩ Z = ∅)
    (a : supportedSections B S hS F W Z hZ) :
    F.obj.map (openObjectHomOfLE B S hS W hD).op
      (supportedSectionsMap B S hS F W Z Z' hZ hZ' hsub hcl a).val = 0 := by
  refine eq_zero_of_supportSection_eq_empty B S hS F _ _
    (Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_)
  have h1 := (supportSection_restrict_subset_preimage B S hS F _ _
    (openObjectHomOfLE B S hS W hD) _) hz
  have h2 : z ∈ D.ι.base ⁻¹' Z := by
    rw [← preimage_openObjectHomOfLE_preimage_ι B S hS W hD Z]
    exact Set.preimage_mono (supportSection_supportedSectionsMap_subset B S hS F W Z Z'
      hZ hZ' hsub hcl a) h1
  exact Set.eq_empty_iff_forall_notMem.1 hempty z.1 ⟨z.2, h2⟩

/-- The canonical open of a locally closed subset with a closed subset of the ambient object
removed. This is the open on which one piece of a clopen decomposition of the subset lives, the
closed subset being one cutting out the complementary piece. -/
public def supportOpenSdiff (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    {C : Set ((SmallEtale.toScheme B S hS).obj W)} (hC : IsClosed C) :
    ((SmallEtale.toScheme B S hS).obj W).Opens :=
  ⟨(supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) \ C,
    (supportOpen B S hS W Z hZ).2.sdiff hC⟩

/-- Removing a closed subset from the canonical open gives a smaller open. -/
public theorem supportOpenSdiff_le (W : SmallEtale B S hS)
    {Z : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    {C : Set ((SmallEtale.toScheme B S hS).obj W)} (hC : IsClosed C) :
    supportOpenSdiff B S hS W hZ hC ≤ supportOpen B S hS W Z hZ := Set.sdiff_subset

/-- A subset of a locally closed `Z` disjoint from the trace `T` of `C` on the canonical open of
`Z` lies in the canonical open with `C` removed. -/
public theorem subset_supportOpenSdiff (W : SmallEtale B S hS)
    {Z Z' T C : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hC : IsClosed C)
    (hCeq : C ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T)
    (hZ' : Z' ⊆ Z) (hdisj : Disjoint Z' T) :
    Z' ⊆ (supportOpenSdiff B S hS W hZ hC : Set ((SmallEtale.toScheme B S hS).obj W)) :=
  fun x hx => ⟨subset_supportOpen B S hS W Z hZ (hZ' hx), fun hxC => Set.disjoint_left.1 hdisj hx
    ((Set.ext_iff.1 hCeq x).1 ⟨hxC, subset_supportOpen B S hS W Z hZ (hZ' hx)⟩)⟩

/-- The canonical open with `C` removed misses the trace of `C` on the canonical open. -/
public theorem supportOpenSdiff_inter_eq_empty (W : SmallEtale B S hS)
    {Z T C : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hC : IsClosed C)
    (hCeq : C ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T) :
    (supportOpenSdiff B S hS W hZ hC : Set ((SmallEtale.toScheme B S hS).obj W)) ∩ T = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun x hx => hx.1.2 ((Set.ext_iff.1 hCeq x).2 hx.2).1

/-- The canonical opens with the closed subsets `C₂` and `C₁` removed cover the canonical open of
`Z` when the traces of `C₁` and `C₂` on it are disjoint. -/
public theorem supportOpen_le_sup_supportOpenSdiff (W : SmallEtale B S hS)
    {Z T₁ T₂ C₁ C₂ : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hC₁ : IsClosed C₁) (hC₂ : IsClosed C₂)
    (hC₁eq : C₁ ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T₁)
    (hC₂eq : C₂ ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T₂)
    (hdisj : Disjoint T₁ T₂) :
    supportOpen B S hS W Z hZ ≤
      supportOpenSdiff B S hS W hZ hC₂ ⊔ supportOpenSdiff B S hS W hZ hC₁ := by
  intro x hx
  by_cases h : x ∈ C₂
  · exact Or.inr ⟨hx, fun hxC₁ => Set.disjoint_left.1 hdisj
      ((Set.ext_iff.1 hC₁eq x).1 ⟨hxC₁, hx⟩) ((Set.ext_iff.1 hC₂eq x).1 ⟨h, hx⟩)⟩
  · exact Or.inl ⟨hx, h⟩

/-- The trace of a closed subset on the canonical open is closed in any open inside it. -/
public theorem isClosed_preimage_ι_of_inter_supportOpen_eq (W : SmallEtale B S hS)
    {Z T C : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hC : IsClosed C)
    (hCeq : C ∩ (supportOpen B S hS W Z hZ : Set ((SmallEtale.toScheme B S hS).obj W)) = T)
    {D : ((SmallEtale.toScheme B S hS).obj W).Opens} (hD : D ≤ supportOpen B S hS W Z hZ) :
    IsClosed (D.ι.base ⁻¹' T) := by
  rw [show D.ι.base ⁻¹' T = D.ι.base ⁻¹' C from Set.ext fun z =>
    ⟨fun h => ((Set.ext_iff.1 hCeq z.1).2 h).1, fun h => (Set.ext_iff.1 hCeq z.1).1 ⟨h, hD z.2⟩⟩]
  exact hC.preimage D.ι.continuous

/-- A section supported on `Z ⊆ T ∪ T'`, restricted to an open of the canonical open of `Z`
missing `T'`, is supported on `T`. -/
public theorem supportSection_restrict_subset_of_inter_eq_empty (W : SmallEtale B S hS)
    {Z T T' : Set ((SmallEtale.toScheme B S hS).obj W)} (hZ : IsLocallyClosed Z)
    (hsub : Z ⊆ T ∪ T') {D : ((SmallEtale.toScheme B S hS).obj W).Opens}
    (hD : D ≤ supportOpen B S hS W Z hZ)
    (hD' : (D : Set ((SmallEtale.toScheme B S hS).obj W)) ∩ T' = ∅)
    (c : supportedSections B S hS F W Z hZ) :
    supportSection B S hS F (openObject B S hS W D)
        (F.obj.map (openObjectHomOfLE B S hS W hD).op c.val) ⊆ D.ι.base ⁻¹' T := by
  intro z hz
  rcases Set.preimage_mono hsub
    (supportSection_restrict_subset_preimage_of_supported B S hS F W hZ hD c hz) with h | h
  · exact h
  · exact (Set.eq_empty_iff_forall_notMem.1 hD' z.1 ⟨z.2, h⟩).elim

/-- For an open support `Z`, the sections supported on `Z` are all the sections over `Z`: a
section over `Z` has support inside `Z` for trivial reasons, so the subgroup cutting out the
support condition on the canonical open is everything after restriction to `Z`. -/
public def supportedSectionsOpenEquivSections (W : SmallEtale B S hS)
    (Z : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (hZ : IsLocallyClosed (Z : Set ((SmallEtale.toScheme B S hS).obj W))) :
    supportedSections B S hS F W (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ ≃+
      F.obj.obj (op (openObject B S hS W Z)) :=
  (locallyClosedSupportEquiv B S hS F W (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (supportOpen B S hS W (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ) Z
    (subset_supportOpen B S hS W (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ)
    Set.Subset.rfl
    (isClosed_supportOpen_preimage B S hS W
      (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ)
    (by
      rw [show Z.ι.base ⁻¹' (Z : Set ((SmallEtale.toScheme B S hS).obj W)) = Set.univ from
        Set.eq_univ_iff_forall.2 fun x => x.2]
      exact isClosed_univ)).trans
  { toFun := fun a => a.val
    invFun := fun a => ⟨a, fun x _ => x.2⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }

/-- The identification of the sections supported on an open support with the sections over it is
restriction. -/
public theorem supportedSectionsOpenEquivSections_apply (W : SmallEtale B S hS)
    (Z : ((SmallEtale.toScheme B S hS).obj W).Opens)
    (hZ : IsLocallyClosed (Z : Set ((SmallEtale.toScheme B S hS).obj W)))
    (a : supportedSections B S hS F W (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ) :
    supportedSectionsOpenEquivSections B S hS F W Z hZ a =
      F.obj.map (openObjectHomOfLE B S hS W
        (subset_supportOpen B S hS W
          (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ)).op a.val :=
  locallyClosedSupportEquiv_restrict B S hS F W
    (Z : Set ((SmallEtale.toScheme B S hS).obj W))
    (supportOpen B S hS W (Z : Set ((SmallEtale.toScheme B S hS).obj W)) hZ) Z _ _ _ _ _ a

section Clopen

variable (W : SmallEtale B S hS) {Z₁ Z₂ : Set ((SmallEtale.toScheme B S hS).obj W)}
  (hZ₁ : IsLocallyClosed Z₁) (hZ₂ : IsLocallyClosed Z₂)
  (hZ : IsLocallyClosed (Z₁ ∪ Z₂))
  (hcl₁ : IsClosed ((Subtype.val : (Z₁ ∪ Z₂ : Set _) → _) ⁻¹' Z₁))
  (hcl₂ : IsClosed ((Subtype.val : (Z₁ ∪ Z₂ : Set _) → _) ⁻¹' Z₂))

/-- The map `H_{Z₁}(F) ⊕ H_{Z₂}(F) ⟶ H_{Z₁ ∪ Z₂}(F)`, the sum of the two transition maps of
Stacks 0F6H along the two inclusions into the union. -/
public def supportedSectionsClopenHom :
    supportedSections B S hS F W Z₁ hZ₁ × supportedSections B S hS F W Z₂ hZ₂ →+
      supportedSections B S hS F W (Z₁ ∪ Z₂) hZ :=
  (supportedSectionsMap B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ Set.subset_union_left hcl₁).coprod
    (supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ Set.subset_union_right hcl₂)

/-- The underlying section of the image of a pair is the sum of the two transported sections. -/
public theorem supportedSectionsClopenHom_val
    (p : supportedSections B S hS F W Z₁ hZ₁ × supportedSections B S hS F W Z₂ hZ₂) :
    (supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ p).val =
      (supportedSectionsMap B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ Set.subset_union_left hcl₁ p.1).val +
      (supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ Set.subset_union_right hcl₂ p.2).val :=
  rfl

/-- The decomposition map is injective: the two components of an element of its kernel are
negatives of each other and are supported on the disjoint `Z₁` and `Z₂`, so both have empty
support. -/
public theorem injective_supportedSectionsClopenHom (hdisj : Disjoint Z₁ Z₂) :
    Function.Injective (supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have hv : (supportedSectionsMap B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ
          Set.subset_union_left hcl₁ p.1).val +
        (supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
          Set.subset_union_right hcl₂ p.2).val = 0 :=
    (supportedSectionsClopenHom_val B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ p).symm.trans
      (congrArg Subtype.val hp)
  have hs₁ := supportSection_supportedSectionsMap_subset B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ
    Set.subset_union_left hcl₁ p.1
  have hs₂ := supportSection_supportedSectionsMap_subset B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
    Set.subset_union_right hcl₂ p.2
  have hneg : supportSection B S hS F
        (openObject B S hS W (supportOpen B S hS W (Z₁ ∪ Z₂) hZ))
        (-(supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
          Set.subset_union_right hcl₂ p.2).val) ⊆
      (supportOpen B S hS W (Z₁ ∪ Z₂) hZ).ι.base ⁻¹' Z₂ :=
    (sectionsSupportedOn B S hS F (openObject B S hS W
      (supportOpen B S hS W (Z₁ ∪ Z₂) hZ))
      ((supportOpen B S hS W (Z₁ ∪ Z₂) hZ).ι.base ⁻¹' Z₂)).neg_mem hs₂
  have heq : (supportedSectionsMap B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ
        Set.subset_union_left hcl₁ p.1).val =
      -(supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
        Set.subset_union_right hcl₂ p.2).val :=
    eq_neg_of_add_eq_zero_left hv
  have h1zero : (supportedSectionsMap B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ
      Set.subset_union_left hcl₁ p.1).val = 0 := by
    refine eq_zero_of_supportSection_eq_empty B S hS F _ _
      (Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_)
    exact Set.disjoint_left.1 hdisj (hs₁ hz) (hneg (heq ▸ hz))
  have h2zero : (supportedSectionsMap B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
      Set.subset_union_right hcl₂ p.2).val = 0 := by
    rwa [h1zero, zero_add] at hv
  exact Prod.ext
    (supportedSectionsMap_injective B S hS F W Z₁ (Z₁ ∪ Z₂) hZ₁ hZ
      Set.subset_union_left hcl₁ ((Subtype.ext h1zero).trans (map_zero _).symm))
    (supportedSectionsMap_injective B S hS F W Z₂ (Z₁ ∪ Z₂) hZ₂ hZ
      Set.subset_union_right hcl₂ ((Subtype.ext h2zero).trans (map_zero _).symm))

/-- The decomposition map is surjective: a section supported on the union restricts, on the two
opens separating the pieces, to sections supported on the pieces, and the sum of the two
transported sections agrees with it on both opens, hence everywhere. -/
public theorem surjective_supportedSectionsClopenHom (hdisj : Disjoint Z₁ Z₂) :
    Function.Surjective (supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂) := by
  intro c
  obtain ⟨C₁, hC₁, hC₁eq⟩ := exists_isClosed_inter_supportOpen_eq B S hS W hZ
    Set.subset_union_left hcl₁
  obtain ⟨C₂, hC₂, hC₂eq⟩ := exists_isClosed_inter_supportOpen_eq B S hS W hZ
    Set.subset_union_right hcl₂
  have h₁ := supportOpenSdiff_le B S hS W hZ hC₂
  have h₂ := supportOpenSdiff_le B S hS W hZ hC₁
  have hZ₁D₁ := subset_supportOpenSdiff B S hS W hZ hC₂ hC₂eq Set.subset_union_left hdisj
  have hZ₂D₂ := subset_supportOpenSdiff B S hS W hZ hC₁ hC₁eq Set.subset_union_right hdisj.symm
  have hD₁Z₂ := supportOpenSdiff_inter_eq_empty B S hS W hZ hC₂ hC₂eq
  have hD₂Z₁ := supportOpenSdiff_inter_eq_empty B S hS W hZ hC₁ hC₁eq
  have hcD₁ := isClosed_preimage_ι_of_inter_supportOpen_eq B S hS W hZ hC₁ hC₁eq h₁
  have hcD₂ := isClosed_preimage_ι_of_inter_supportOpen_eq B S hS W hZ hC₂ hC₂eq h₂
  have hr₁ := supportSection_restrict_subset_of_inter_eq_empty B S hS F W hZ subset_rfl h₁
    hD₁Z₂ c
  have hr₂ := supportSection_restrict_subset_of_inter_eq_empty B S hS F W hZ
    (Set.union_comm Z₁ Z₂).subset h₂ hD₂Z₁ c
  refine ⟨((locallyClosedSupportEquiv B S hS F W Z₁ (supportOpen B S hS W Z₁ hZ₁)
      (supportOpenSdiff B S hS W hZ hC₂) (subset_supportOpen B S hS W Z₁ hZ₁) hZ₁D₁
      (isClosed_supportOpen_preimage B S hS W Z₁ hZ₁) hcD₁).symm ⟨_, hr₁⟩,
    (locallyClosedSupportEquiv B S hS F W Z₂ (supportOpen B S hS W Z₂ hZ₂)
      (supportOpenSdiff B S hS W hZ hC₁) (subset_supportOpen B S hS W Z₂ hZ₂) hZ₂D₂
      (isClosed_supportOpen_preimage B S hS W Z₂ hZ₂) hcD₂).symm ⟨_, hr₂⟩), ?_⟩
  refine Subtype.ext (sub_eq_zero.mp (eq_zero_of_map_openObjectHomOfLE_eq_zero B S hS F W
    h₁ h₂ (supportOpen_le_sup_supportOpenSdiff B S hS W hZ hC₁ hC₂ hC₁eq hC₂eq hdisj) _
    ?_ ?_))
  all_goals rw [map_sub, sub_eq_zero, supportedSectionsClopenHom_val, map_add]
  · rw [map_openObjectHomOfLE_supportedSectionsMap_val B S hS F W hZ₁
      hZ Set.subset_union_left hcl₁ h₁ hZ₁D₁ hcD₁,
      map_openObjectHomOfLE_supportedSectionsMap_eq_zero B S hS F W hZ₂ hZ
        Set.subset_union_right hcl₂ h₁ hD₁Z₂, add_zero]
  · rw [map_openObjectHomOfLE_supportedSectionsMap_eq_zero B S hS F W
      hZ₁ hZ Set.subset_union_left hcl₁ h₂ hD₂Z₁,
      map_openObjectHomOfLE_supportedSectionsMap_val B S hS F W hZ₂ hZ Set.subset_union_right
        hcl₂ h₂ hZ₂D₂ hcD₂, zero_add]

/-- Along a disjoint decomposition of a locally closed subset into two locally closed pieces, each
closed in it, the sections supported on the subset are the direct sum of the sections supported on
the two pieces. -/
public theorem bijective_supportedSectionsClopenHom (hdisj : Disjoint Z₁ Z₂) :
    Function.Bijective (supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂) :=
  ⟨injective_supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ hdisj,
    surjective_supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ hdisj⟩

/-- `H_{Z₁ ∪ Z₂}(F) ≅ H_{Z₁}(F) ⊕ H_{Z₂}(F)` for a disjoint decomposition of a locally closed
subset into two locally closed pieces, each closed in it. -/
public def supportedSectionsClopenEquiv (hdisj : Disjoint Z₁ Z₂) :
    supportedSections B S hS F W Z₁ hZ₁ × supportedSections B S hS F W Z₂ hZ₂ ≃+
      supportedSections B S hS F W (Z₁ ∪ Z₂) hZ :=
  AddEquiv.ofBijective (supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂)
    (bijective_supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ hdisj)

/-- The decomposition isomorphism is the sum of the two transition maps. -/
@[simp]
public theorem supportedSectionsClopenEquiv_apply (hdisj : Disjoint Z₁ Z₂)
    (p : supportedSections B S hS F W Z₁ hZ₁ × supportedSections B S hS F W Z₂ hZ₂) :
    supportedSectionsClopenEquiv B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ hdisj p =
      supportedSectionsClopenHom B S hS F W hZ₁ hZ₂ hZ hcl₁ hcl₂ p :=
  rfl

end Clopen

end AlgebraicGeometry.SmallEtale

end
