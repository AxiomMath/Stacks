module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratorsAgreeLocally
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCech
import StacksCore.Tactic.StacksAttribute

/-!
# The object of Tag 099E does not depend on the chosen generating family

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` and `g_1, …, g_s` be two finite families of
global sections of `𝒪` which, over *every* object, span the same ideal of sections. Then the two
objects `K(f) ⟶ 𝒪` and `K(g) ⟶ 𝒪` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/SheafifiedCech.lean` are
isomorphic in `D(𝒪)` over `𝒪`.

This is the independence [Stacks, Tag 099E] needs of the finitely generated ideal `I ⊆ ℐ(U)`
chosen to present `ℐ|_U`. The hypothesis — that the two families span the same ideal of *sections*
over every object, not merely that they generate the same ideal *sheaf* — is what
`AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq` of `GeneratorsAgreeLocally.lean` supplies
after passing to a covering, which is also exactly how the source proceeds.

## Main results

* `AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_forall_span_eq`: **the objects of two
  families spanning the same ideal of sections over every object are isomorphic in `D(𝒪)`,
  compatibly with the maps to `𝒪`.**
* `AlgebraicGeometry.RingedSite.exists_mem_sieve_iso_sheafifiedCech`: **[Stacks, Tag 099E]'s
  independence of the choice of `I`** — two finite families of global sections generating the same
  sheaf of ideals give, on the slices over the arrows of a covering sieve of any object, the same
  object of `D(𝒪)` over the structure sheaf.

## Implementation notes

The comparison is the zig-zag through the concatenated family `f_1, …, f_r, g_1, …, g_s`, whose
two restrictions onto the blocks are maps of complexes and quasi-isomorphisms: the concatenated
family spans the common ideal over every object
(`Stacks.IdealCechComplex.span_range_append_eq`), so
`AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict` applies to each block. At the ring
level the same zig-zag realizes the canonical comparison of
`Stacks.IdealCechComplex.restrictObjHom_comp_canonicalHom`; the point of using it here rather
than the canonical comparison itself is that its two legs are maps of *complexes*, so they
sheafify, while a comparison in the derived category of each ring of sections does not.

No direct comparison of the two families is produced: the restriction maps go from the
concatenation to each block, and only after inverting one of them in `D(𝒪)` is there a map from
`K(f)` to `K(g)`. That is why the conclusion is an existential rather than a named morphism —
as it is in the source, and as the shape of the statement must be, a choice of generating family
functorial in the object being impossible
(`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`).

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

section Independence

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The values of a concatenated family of global sections are the concatenation of the
values. -/
theorem cechFamily_append (V : X.Cᵒᵖ) :
    cechFamily X (Fin.append f g) V =
      Fin.append (cechFamily X f V) (cechFamily X g V) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    exact congrArg (fun h => globalSectionVal h V) (Fin.append_left f g i)
  · rw [Fin.append_right]
    exact congrArg (fun h => globalSectionVal h V) (Fin.append_right f g j)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The concatenated family spans the common ideal of sections over every object**, when the
two families do. -/
theorem span_range_restrictGlobalSections_append (V : X.Cᵒᵖ)
    (hV : Ideal.span (Set.range (restrictGlobalSections X f V)) =
      Ideal.span (Set.range (restrictGlobalSections X g V))) :
    Ideal.span (Set.range (restrictGlobalSections X (Fin.append f g) V)) =
      Ideal.span (Set.range (restrictGlobalSections X f V)) := by
  have hkey : Ideal.span (Set.range (Fin.append (cechFamily X f V) (cechFamily X g V))) =
      Ideal.span (Set.range (cechFamily X f V)) :=
    Stacks.IdealCechComplex.span_range_append_eq (cechFamily X f V) (cechFamily X g V) hV
  exact (congrArg (fun m => Ideal.span (Set.range m)) (cechFamily_append X f g V)).trans hkey

/-- The restriction of the sheafified Čech complex to a subfamily spanning the same ideal of
sections over every object becomes an isomorphism in `D(𝒪)`. -/
private theorem isIso_Q_map_sheafifiedCechRestrict (e : Fin r ↪o Fin s)
    (he : ∀ i, g (e i) = f i)
    (hspan : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X g V)) =
        Ideal.span (Set.range (restrictGlobalSections X f V))) :
    IsIso (DerivedCategory.Q.map (sheafifiedCechRestrict X f g e he)) := by
  have := quasiIso_sheafifiedCechRestrict X f g e he hspan
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- **The objects of [Stacks, Tag 099E] attached to two families spanning the same ideal of
sections over every object are isomorphic in `D(𝒪)` over `𝒪`.**

The isomorphism is the zig-zag through the concatenated family: both restrictions of
`K(f_1, …, f_r, g_1, …, g_s)` onto its two blocks are quasi-isomorphisms and maps over `𝒪`, so
after sheafifying and passing to `D(𝒪)` one of them can be inverted. -/
theorem exists_iso_sheafifiedCech_of_forall_span_eq
    (hspan : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X f V)) =
        Ideal.span (Set.range (restrictGlobalSections X g V))) :
    ∃ e : DerivedCategory.Q.obj (sheafifiedCech X f) ≅
        DerivedCategory.Q.obj (sheafifiedCech X g),
      e.hom ≫ DerivedCategory.Q.map (sheafifiedCechAugmentation X g) =
        DerivedCategory.Q.map (sheafifiedCechAugmentation X f) := by
  have hfh : ∀ i, Fin.append f g (Fin.castAddOrderEmb s i) = f i := fun i => Fin.append_left f g i
  have hgh : ∀ j, Fin.append f g (Fin.natAddOrderEmb r j) = g j := fun j => Fin.append_right f g j
  have hsf : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X (Fin.append f g) V)) =
        Ideal.span (Set.range (restrictGlobalSections X f V)) := fun V =>
    span_range_restrictGlobalSections_append X f g V (hspan V)
  have hsg : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X (Fin.append f g) V)) =
        Ideal.span (Set.range (restrictGlobalSections X g V)) := fun V =>
    (hsf V).trans (hspan V)
  have := isIso_Q_map_sheafifiedCechRestrict X f (Fin.append f g) (Fin.castAddOrderEmb s) hfh hsf
  have := isIso_Q_map_sheafifiedCechRestrict X g (Fin.append f g) (Fin.natAddOrderEmb r) hgh hsg
  refine ⟨(asIso (DerivedCategory.Q.map
      (sheafifiedCechRestrict X f (Fin.append f g) (Fin.castAddOrderEmb s) hfh))).symm ≪≫
    asIso (DerivedCategory.Q.map
      (sheafifiedCechRestrict X g (Fin.append f g) (Fin.natAddOrderEmb r) hgh)), ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, ← Functor.map_comp,
    sheafifiedCechRestrict_comp_augmentation,
    ← sheafifiedCechRestrict_comp_augmentation X f (Fin.append f g) (Fin.castAddOrderEmb s) hfh,
    Functor.map_comp, IsIso.inv_hom_id_assoc]

end Independence

section Covering

variable (X : RingedSite.{u, u, u})
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}] {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}] in
/-- The restrictions of a family of global sections to a slice are, over an object of the slice,
the restrictions of the family to its underlying object. -/
theorem restrictGlobalSections_globalSectionOver (Y : X.C) (V : (Over Y)ᵒᵖ) :
    restrictGlobalSections (X.over Y) (fun i => globalSectionOver X Y (f i)) V =
      restrictGlobalSections X f (op V.unop.left) :=
  funext fun i => globalSectionVal_globalSectionOver X Y (f i) V

omit [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}] in
/-- **[Stacks, Tag 099E]'s independence of the choice of the finitely generated ideal, after
passing to a covering.** Let `f_1, …, f_r` and `g_1, …, g_s` be two finite families of global
sections of `𝒪` generating the same sheaf of ideals `ℐ`. Then every object `U` has a covering
sieve along each arrow `Y → U` of which the two objects of [Stacks, Tag 099E] on the slice
`(𝒞/Y, 𝒪_Y)` are isomorphic in `D(𝒪_Y)`, compatibly with their maps to `𝒪_Y`.

This is the step the source states as a hint and then uses: the covering is the one of
`AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq`, on which the two families span the same
ideal of *sections*; because a sieve is stable under precomposition that persists at every object
of every slice `𝒞/Y` above it, which is the hypothesis of
`AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_forall_span_eq` there. -/
theorem exists_mem_sieve_iso_sheafifiedCech
    (h : idealOfGlobalSections X f = idealOfGlobalSections X g) (U : X.C) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃Y : X.C⦄ (a : Y ⟶ U), S a →
      ∃ e : DerivedCategory.Q.obj
            (sheafifiedCech (X.over Y) (fun i => globalSectionOver X Y (f i))) ≅
          DerivedCategory.Q.obj
            (sheafifiedCech (X.over Y) (fun j => globalSectionOver X Y (g j))),
        e.hom ≫ DerivedCategory.Q.map (sheafifiedCechAugmentation (X.over Y)
            (fun j => globalSectionOver X Y (g j))) =
          DerivedCategory.Q.map (sheafifiedCechAugmentation (X.over Y)
            (fun i => globalSectionOver X Y (f i))) := by
  obtain ⟨S, hS, hspan⟩ := exists_mem_sieve_span_eq X f g h U
  refine ⟨S, hS, fun {Y} a ha => exists_iso_sheafifiedCech_of_forall_span_eq (X.over Y) _ _
    fun V => ?_⟩
  have hmem : S (V.unop.hom ≫ a) := S.downward_closed ha V.unop.hom
  have hV := hspan (V.unop.hom ≫ a) hmem
  rw [restrictGlobalSections_globalSectionOver X f Y V,
    restrictGlobalSections_globalSectionOver X g Y V]
  exact hV

end Covering

end AlgebraicGeometry.RingedSite

end
