module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Unibranch
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion

/-!
# An unramified morphism from a connected scheme over a geometrically unibranch base

Let `f : X ⟶ Y` be unramified with `X` connected and `Y` integral and geometrically unibranch. If
one irreducible component of `X` dominates `Y`, that is, the closure of its image is all of `Y`,
then `f` is étale and `X` is irreducible.

## Main results

* `AlgebraicGeometry.etale_of_unramified_of_dominant_component`: `f` is étale.
* `AlgebraicGeometry.irreducibleSpace_of_unramified_of_dominant_component`: `X` is irreducible.

## References

* [SGA 1, Exposé I, Corollary 9.11]
* [Stacks Project, Tag 0GS9](https://stacks.math.columbia.edu/tag/0GS9)
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The generic point of an irreducible component of a scheme is a generic point of it. -/
private theorem isGenericPoint_genericPoint_component
    {U : Scheme.{u}} (C : irreducibleComponents U) :
    IsGenericPoint C.2.1.genericPoint (C : Set U) :=
  C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)

/-- Along a flat morphism to an integral scheme the generic point of an irreducible component of
the source maps to the generic point of the target. -/
private theorem map_genericPoint_of_flat
    {U V : Scheme.{u}} (g : U ⟶ V) [Flat g] [IsIntegral V]
    (C : irreducibleComponents U) : g C.2.1.genericPoint = genericPoint V := by
  have hξ := isGenericPoint_genericPoint_component C
  obtain ⟨ξ', hξ'ξ, hξ'η⟩ :=
    Flat.generalizingMap g ((genericPoint_spec V).specializes (Set.mem_univ (g _)))
  have hsub : (C : Set U) ⊆ closure ({ξ'} : Set U) := by
    rw [← hξ]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξ'ξ.mem_closure) isClosed_closure
  have hξ'C : IsGenericPoint ξ' (C : Set U) :=
    Set.Subset.antisymm (C.2.2 isIrreducible_singleton.closure hsub) hsub
  exact (hξ'C.eq hξ) ▸ hξ'η

/-- The source of an étale morphism of affine schemes to an integral scheme has finitely many
irreducible components. -/
private theorem finite_irreducibleComponents_of_etale_of_isAffine
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] [IsIntegral V] (g : U ⟶ V) [Etale g] :
    (irreducibleComponents U).Finite := by
  obtain ⟨hft, hlqf⟩ := locallyQuasiFinite_of_etale g
  have : LocallyOfFiniteType g := hft
  have : QuasiCompact g := inferInstance
  exact Set.Finite.subset
    ((finite_setOf_mapsTo_and_quasiFiniteAt g (genericPoint V)).image
      fun x ↦ closure ({x} : Set U)) fun C hC ↦ ⟨hC.1.genericPoint,
    ⟨map_genericPoint_of_flat g ⟨C, hC⟩, (forall_quasiFiniteAt_iff g).mpr ⟨hft, hlqf⟩ _⟩,
    isGenericPoint_genericPoint_component ⟨C, hC⟩⟩

/-- In a space with finitely many irreducible components, no two of which pass through a common
point, every irreducible component is open. -/
@[ega "I 6.1.10" "(d) ⇒ (a)"]
theorem isOpen_of_mem_irreducibleComponents_of_finite
    {T : Type*} [TopologicalSpace T] (hfin : (irreducibleComponents T).Finite)
    (hunique : ∀ t (C D : irreducibleComponents T),
      t ∈ (C : Set T) → t ∈ (D : Set T) → C = D)
    (C : irreducibleComponents T) : IsOpen (C : Set T) := by
  have hcompl : (C : Set T)ᶜ = ⋃₀ (irreducibleComponents T \ {(C : Set T)}) := by
    ext t
    constructor
    · intro ht
      let D : irreducibleComponents T :=
        ⟨irreducibleComponent t, irreducibleComponent_mem_irreducibleComponents t⟩
      exact ⟨D, ⟨D.2, fun h ↦
        ht (Subtype.ext (Set.mem_singleton_iff.mp h) ▸ mem_irreducibleComponent)⟩,
        mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, htD⟩ htC
      exact hne (Set.mem_singleton_iff.mpr
        (congrArg Subtype.val (hunique t ⟨D, hD⟩ C htD htC)))
  rw [← isClosed_compl_iff, hcompl]
  exact hfin.sdiff.isClosed_sUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1

/-- An unramified morphism to an integral geometrically unibranch scheme is étale at every point
of an irreducible component of its source whose image is dense. -/
@[ega "IV 18.10.1" "(i), special case"]
private theorem etaleAt_of_mem_dominant_component
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [Unramified f]
    (hY : IsGeometricallyUnibranch Y) (Z : irreducibleComponents X)
    (hZ : closure (f '' (Z : Set X)) = Set.univ) {x : X} (hx : x ∈ (Z : Set X)) :
    EtaleAt f x := by
  have hη := isGenericPoint_genericPoint_component Z
  have hgeneric : f Z.2.1.genericPoint = genericPoint Y :=
    (hZ ▸ hη.image f.continuous).eq (genericPoint_spec Y)
  have : LocallyOfFiniteType f :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp ‹Unramified f›).1
  exact etaleAt_of_unramifiedAt_of_specializes_genericPoint f (hY (f x))
    (hη.specializes hx) hgeneric (Unramified.unramifiedAt x)

/-- For an unramified morphism from a connected scheme to an integral geometrically unibranch
scheme, if some irreducible component of the source has dense image, then one such component is
the whole source. -/
@[ega "IV 18.10.3" "partial", sga "1 I 9.11" "irreducibility of X", sga "3 X 5.14.0" "partial"]
private theorem dominant_component_eq_univ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [Unramified f] [ConnectedSpace X]
    (hY : IsGeometricallyUnibranch Y)
    (hdom : ∃ Z : irreducibleComponents X, closure (f '' (Z : Set X)) = Set.univ) :
    ∃ Z : irreducibleComponents X,
      closure (f '' (Z : Set X)) = Set.univ ∧ (Z : Set X) = Set.univ := by
  obtain ⟨Z, hZ⟩ := hdom
  have hZopen : IsOpen (Z : Set X) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨U, hU, hxU, V, hV, hUV, hEt⟩ := etaleAt_of_mem_dominant_component f hY Z hZ hx
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    have : Nonempty V := ⟨⟨f x, hUV hxU⟩⟩
    have : IsIntegral V.toScheme := inferInstance
    have hres : Etale (f.resLE V U hUV) := etale_resLE_of_appLE_etale f U hU V hV hUV hEt
    have hcomp : Etale (U.ι ≫ f) := by
      rw [← Scheme.Hom.resLE_comp_ι f hUV]
      infer_instance
    have hfin : (irreducibleComponents U.toScheme).Finite :=
      finite_irreducibleComponents_of_etale_of_isAffine (f.resLE V U hUV)
    have hunique : ∀ y (C D : irreducibleComponents U.toScheme),
        y ∈ (C : Set U.toScheme) → y ∈ (D : Set U.toScheme) → C = D := by
      intro y C D hyC hyD
      obtain ⟨K, -, hKuniq⟩ :=
        (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent Y ((U.ι ≫ f) y)).mp
          (hY ((U.ι ≫ f) y)) (EtaleNeighborhood.ofEtale (U.ι ≫ f) y)
      exact (hKuniq C hyC).trans (hKuniq D hyD).symm
    have hCmem : U.ι ⁻¹' (Z : Set X) ∈ irreducibleComponents U.toScheme :=
      preimage_mem_irreducibleComponents Z.2 U.ι.isOpenEmbedding ⟨x, hx, ⟨x, hxU⟩, rfl⟩
    have hCopen : IsOpen (U.ι ⁻¹' (Z : Set X)) :=
      isOpen_of_mem_irreducibleComponents_of_finite hfin hunique ⟨_, hCmem⟩
    refine Filter.mem_of_superset
      ((U.ι ''ᵁ ⟨U.ι ⁻¹' (Z : Set X), hCopen⟩).isOpen.mem_nhds ⟨⟨x, hxU⟩, hx, rfl⟩) ?_
    rintro y ⟨z, hz, rfl⟩
    exact hz
  exact ⟨Z, hZ, (show IsClopen (Z : Set X) from
    ⟨isClosed_of_mem_irreducibleComponents _ Z.2, hZopen⟩).eq_univ Z.2.1.nonempty⟩

/-- An unramified morphism from a connected scheme to an integral geometrically unibranch scheme
is étale as soon as one irreducible component of its source dominates the target. -/
@[stacks 0GS9 "etaleness", sga "1 I 9.11" "f étale", ega "IV 18.10.3" "f étale"]
theorem etale_of_unramified_of_dominant_component
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [Unramified f] [ConnectedSpace X]
    (hY : IsGeometricallyUnibranch Y)
    (hdom : ∃ Z : irreducibleComponents X, closure (f '' (Z : Set X)) = Set.univ) :
    Etale f := by
  obtain ⟨Z, hZ, hZeq⟩ := dominant_component_eq_univ f hY hdom
  exact (etale_iff_forall_etaleAt f).2 fun x ↦
    etaleAt_of_mem_dominant_component f hY Z hZ (hZeq ▸ Set.mem_univ x)

/-- The source of an unramified morphism from a connected scheme to an integral geometrically
unibranch scheme is irreducible as soon as one of its irreducible components dominates the
target. -/
@[stacks 0GS9 "irreducibility", sga "1 I 9.11" "X irreducible", ega "IV 18.10.3" "X irreducible"]
theorem irreducibleSpace_of_unramified_of_dominant_component
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [Unramified f] [ConnectedSpace X]
    (hY : IsGeometricallyUnibranch Y)
    (hdom : ∃ Z : irreducibleComponents X, closure (f '' (Z : Set X)) = Set.univ) :
    IrreducibleSpace X := by
  obtain ⟨Z, -, hZeq⟩ := dominant_component_eq_univ f hY hdom
  refine (irreducibleSpace_def X).mpr ?_
  change IsIrreducible (Set.univ : Set X)
  rw [← hZeq]
  exact Z.2.1

end AlgebraicGeometry

end
