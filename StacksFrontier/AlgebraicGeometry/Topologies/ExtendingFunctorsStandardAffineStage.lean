module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCoveringSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardAffineDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringsBaseChange

/-!
# The restricted sheaf condition at a stage of a presentation

Let `S` be a scheme, let `𝒞` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW and let `F : 𝒞ᵒᵖ ⥤ Set` satisfy conditions (a), (b) and (c). Stacks 0GDW reads the
sheaf condition for the extension off at the stages of the presentation produced by
`AlgebraicGeometry.ExtendingFunctors.exists_baseChangePresentation_of_isStandardCovering` before
passing to the filtered colimit. This file supplies the reading at a stage.

A stage of a base-changed presentation is affine and of finite presentation over an affine open of
`S`, hence isomorphic to an object of the subcategory, but it is not literally such an object;
and the standard covering of the stage is the base change of the covering of the least stage,
again only up to the identification of a fibre product in `Sch/S` with the fibre product of the
underlying schemes. Both discrepancies are isomorphisms of the *sources* of the covering family
over a fixed target, and both are absorbed here: a standard covering stays standard when its
sources are replaced by isomorphic schemes
(`AlgebraicGeometry.IsStandardCovering.of_iso_source`) and the sheaf condition for a family of
arrows is unchanged by the same replacement
(`AlgebraicGeometry.ExtendingFunctors.isSheafFor_ofArrows_of_iso`), because the two families
generate the same sieve.

## Main results

* `AlgebraicGeometry.IsStandardCovering.of_iso_source`: a standard `τ`-covering stays a standard
  `τ`-covering when its sources are replaced by isomorphic schemes over the same target.
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isStandardCovering`: condition (c)
  read for the extension, namely the sheaf condition for the extension and a standard
  `τ`-covering, by objects isomorphic to objects of the subcategory, of an object of the
  subcategory which is affine and of finite presentation over an affine open of `S`.

## Implementation notes

Only the last clause of `AlgebraicGeometry.IsStandardCovering` looks at the topology, and the
transport of that clause along an isomorphism of the source is, for the two topologies whose
clause is a condition on the ring map, the invariance of that condition under isomorphism in the
arrow category (`AlgebraicGeometry.isStandardSmooth_iff_of_arrow_iso`,
`AlgebraicGeometry.isStandardSyntomic_iff_of_arrow_iso`); for the fppf and étale topologies it is
the invariance of a property of morphisms under precomposition with an isomorphism, and for the
Zariski topology it is the composition of two isomorphisms. The properties of morphisms are
discharged by lemmas stated outside the case analysis on the topology.

## References

* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry

/-! ### Properties of morphisms under precomposition with an isomorphism -/

/-- Flatness is invariant under precomposition with an isomorphism. -/
lemma flat_isoComp {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {g : Y ⟶ Z} (hg : Flat g) :
    Flat (e ≫ g) :=
  have := hg
  inferInstance

/-- Étaleness is invariant under precomposition with an isomorphism. -/
lemma etale_isoComp {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] {g : Y ⟶ Z} (hg : Etale g) :
    Etale (e ≫ g) :=
  have := hg
  inferInstance

/-! ### Standard coverings and isomorphisms of the sources -/

/-- **A standard covering is unchanged by replacing its sources by isomorphic schemes.** If
`{f i : U i ⟶ T}` is a standard `τ`-covering and `e i : U' i ≅ U i`, then the family
`{(e i).hom ≫ f i : U' i ⟶ T}` is a standard `τ`-covering. -/
theorem IsStandardCovering.isoComp {τ : CoveringTopology} {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {U U' : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering τ U f)
    (e : ∀ i, U' i ≅ U i) :
    IsStandardCovering τ U' (fun i => (e i).hom ≫ f i) := by
  have haff : ∀ i, IsAffine (U' i) := fun i =>
    have := h.affine_source i
    IsAffine.of_isIso (e i).hom
  have hsurj : ∀ i, Function.Surjective ((e i).hom : U' i → U i) := fun i y =>
    ⟨(e i).inv y, Scheme.inv_hom_apply (e i) y⟩
  have hrange : ∀ i, Set.range ((e i).hom ≫ f i) = Set.range (f i) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.2 (hsurj i), Set.image_univ]
  refine ⟨h.finite_index, haff, Eq.trans (Set.iUnion_congr hrange) h.jointly_surjective, ?_⟩
  intro i
  have hsrc := h.affine_source i
  have hsrc' := haff i
  have hi := h.standard i
  have harr : Arrow.mk ((e i).hom ≫ f i) ≅ Arrow.mk (f i) :=
    Arrow.isoMk (e i) (Iso.refl T) (by simp)
  cases τ with
  | fppf =>
      exact ⟨flat_isoComp (e i).hom hi.1,
        ExtendingFunctors.finitePresentation_isoComp (e i).hom hi.2⟩
  | syntomic => exact (isStandardSyntomic_iff_of_arrow_iso _ (f i) harr).2 hi
  | smooth => exact (isStandardSmooth_iff_of_arrow_iso _ (f i) harr).2 hi
  | etale => exact etale_isoComp (e i).hom hi
  | zariski =>
      obtain ⟨a, e₀, he₀⟩ := hi
      exact ⟨a, (e i) ≪≫ e₀, by rw [he₀, Iso.trans_hom, Category.assoc]⟩

/-- **A standard covering is unchanged by replacing its sources by isomorphic schemes**, with the
new family given rather than constructed. -/
theorem IsStandardCovering.of_iso_source {τ : CoveringTopology} {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {U U' : I → Scheme.{u}} {f : ∀ i, U i ⟶ T} (h : IsStandardCovering τ U f)
    (e : ∀ i, U' i ≅ U i) (f' : ∀ i, U' i ⟶ T) (hf' : ∀ i, f' i = (e i).hom ≫ f i) :
    IsStandardCovering τ U' f' := by
  obtain rfl : f' = fun i => (e i).hom ≫ f i := funext hf'
  exact h.isoComp e

namespace ExtendingFunctors

/-! ### Condition (c) read for the extension -/

variable {S : Scheme.{u}}

/-- **Condition (c) read for the extension.** Let `V` be an object of the full subcategory which
is affine and of finite presentation over an affine open `U` of `S`, and let `{f i : W i ⟶ V}` be
a standard `τ`-covering of `V` in `Sch/S` each of whose members is isomorphic to an object of the
full subcategory. Then the extension satisfies the sheaf condition for `{f i}`.

This is the sheaf condition read off at a stage of the presentation of Stacks 0GDW. Neither the
members of the covering nor, after base change, the fibre products are literally objects of the
subcategory; replacing them by isomorphic objects of the subcategory changes neither the
standardness of the covering
(`AlgebraicGeometry.IsStandardCovering.of_iso_source`) nor the sheaf condition
(`AlgebraicGeometry.ExtendingFunctors.isSheafFor_ofArrows_of_iso`), after which condition (c)
applies and `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isSheafFor` passes from
the subcategory to `Sch/S`. -/
theorem isSheafFor_extension_of_isStandardCovering (τ : CoveringTopology)
    {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (haF : IsZariskiSheafOnSubcategory P F) (hbF : PreservesAffineLimitsOnSubcategory P F)
    (hcF : IsStandardAffineSheafOnSubcategory.{max w (u + 1), u, v} τ P F)
    {V : Over S} (hPV : P V) (hVaff : IsAffine V.left) (U : S.affineOpens)
    (gV : V.left ⟶ U.1.toScheme) (hgV : gV ≫ U.1.ι = V.hom) (hgVfp : FinitePresentation gV)
    {ι : Type v} (W : ι → Over S) (f : ∀ i, W i ⟶ V)
    (hWmem : ∀ i, ∃ Z : Over S, P Z ∧ Nonempty (W i ≅ Z))
    (hstd : @IsStandardCovering τ V.left hVaff ι (fun i => (W i).left)
      (fun i => (f i).left)) :
    (Presieve.ofArrows W f).IsSheafFor (extension P F) := by
  classical
  choose Z hZ hziso using hWmem
  let ε : ∀ i, W i ≅ Z i := fun i => (hziso i).some
  let V' : P.FullSubcategory := ⟨V, hPV⟩
  let Z' : ι → P.FullSubcategory := fun i => ⟨Z i, hZ i⟩
  let fZ : ∀ i, Z' i ⟶ V' := fun i => ObjectProperty.homMk ((ε i).inv ≫ f i)
  have hstd' : @IsStandardCovering τ V'.obj.left hVaff ι (fun i => (Z' i).obj.left)
      (fun i => (P.ι.map (fZ i)).left) := by
    refine hstd.of_iso_source (fun i => ((Over.forget S).mapIso (ε i)).symm) _ fun i => ?_
    rfl
  have hshF : (Presieve.ofArrows Z' fZ).IsSheafFor F :=
    hcF V' hVaff U gV hgV hgVfp Z' fZ hstd'
  have hshE : (Presieve.ofArrows (fun i => (Z' i).obj) (fun i => (fZ i).hom)).IsSheafFor
      (extension P F) :=
    isSheafFor_extension_of_isSheafFor F hP1 hP2 haF hbF V' Z' fZ hshF
  refine isSheafFor_ofArrows_of_iso (Iso.refl V) ε f (fun i => (ε i).inv ≫ f i)
    (fun i => ?_) hshE
  rw [Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

end ExtendingFunctors

end AlgebraicGeometry

end
