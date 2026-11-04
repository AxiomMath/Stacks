module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# A finite constant sheaf on the small étale site is representable by a finite étale scheme

Let `V` be a scheme belonging to a chosen big étale site and let `ι` be a finite index type.
The disjoint union `∐_{i : ι} V` of copies of `V`, with its fold map, is an object of the small
étale site of `V` whose structure morphism is finite étale, and the sheaf it represents is the
constant sheaf on `ι`: a `W`-point of `∐_{i : ι} V` over `V` is, locally on `W`, one of the `ι`
components.

This is the converse of
`Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable` for a sheaf which is
*constant* with finite value, that is, the base case of the other direction of Stacks 59.64.4
(Tag 03RV). The general case — a finite *locally* constant sheaf — is this statement on each
member of a trivializing covering together with effective descent for schemes affine over the base
(Stacks 0245), which is carried as an explicit hypothesis; see the implementation notes.

## Main definitions

* `Stacks.EtaleCohomology.splitObj` — the object `∐_{i : ι} V` of the small étale site of `V`.
* `Stacks.EtaleCohomology.isSplitOverSigmaDescId` — its sheet data over `V` itself: the sheets
  are the components of the coproduct.
* `Stacks.EtaleCohomology.constToSplitYoneda` — the comparison map from the constant presheaf on
  `ι` to the presheaf represented by `∐_{i : ι} V`.

## Main results

* `Stacks.EtaleCohomology.isFinite_hom_splitObj` — the structure morphism of `∐_{i : ι} V` is
  finite.
* `Stacks.EtaleCohomology.constantSheafIsoSheafifiedYonedaSplitObj` — the constant sheaf on `ι`
  on the small étale site of `V` is the sheaf represented by `∐_{i : ι} V`.
* `Stacks.EtaleCohomology.exists_finiteEtaleRepresentable_constantSheaf` — every finite constant
  sheaf of sets on the small étale site of `V` is represented by an object of the site whose
  structure morphism is finite, in exactly the form Tag 03RV asserts.
* `Stacks.EtaleCohomology.exists_finiteEtaleRepresentable_of_isConstant` — the same for a sheaf
  merely isomorphic to a finite constant sheaf.

## Implementation notes

The three obligations for `∐_{i : ι} V` to be an object of the small étale site are discharged
separately. The size bound is `AlgebraicGeometry.schemeSize_coproduct_le` applied at the size of
`V` itself, which bounds both the index type — finite, hence of cardinality at most `ℵ₀ ≤ size V`
— and each component. Finiteness of the fold map is `AlgebraicGeometry.isFinite_sigmaDesc`, and
étaleness holds because étale morphisms are Zariski-local at the source.

The two local statements about the comparison map are not proved from scratch: the coproduct
decomposition of a point is exactly `Stacks.Etale.IsSplitOver`, so
`Stacks.Etale.isSplitOverOfIso` is applied to the canonical isomorphism
`(∐_{i : ι} V) ×_V V ≅ ∐_{i : ι} V` and the resulting sheet data supplies both the open covering
on which a point agrees with a component and the emptiness of the locus where two distinct
components agree. The members of that covering are objects of the site by
`Stacks.EtaleCohomology.openObj`, which is Stacks 000R (3).

The passage from the constant presheaf to the constant sheaf is
`Stacks.ConstantSheaf.presheafToSheafObjIso`: `CategoryTheory.constantSheaf` is by definition the
sheafification of the constant presheaf, so a locally bijective map from the latter to the
presheaf represented by `∐_{i : ι} V` identifies it with the sheafified representable.

### How this enters Tag 03RV

For a finite locally constant `F` the trivializing covering `{V_j ⟶ X}` of Tag 093Q (3) makes
each restriction `F|_{V_j}` constant with finite value, and the statements here produce a finite
étale scheme over `V_j` representing it. Assembling those into a single object of the small étale
site of `X` is effective descent for schemes affine over the base along an étale covering, Stacks
0245, which this library has only in its affine, ring-theoretic form
(`Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat`) and which therefore
enters as an explicit hypothesis of
`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable_of_descent`, the
equivalence of Tag 03RV.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

/-! ### A constancy criterion on a site, as opposed to on a localized site -/

namespace Stacks.ConstantSheaf

/-- **The constancy criterion on the site itself.** If a constant presheaf maps locally
bijectively to a presheaf `P`, then the sheafification of `P` is the constant sheaf with the same
value. This is the companion of `Stacks.ConstantSheaf.constantSheafObjIsoOverPullback`, which is
the same statement for a localized site, and like it has to be stated for an abstract site: at a
concrete one the universe unification `max ?u ?v ≟ w` behind the local bijectivity of
`CategoryTheory.toSheafify` does not fire. -/
public def constantSheafObjIsoSheafification {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) {E : Type max w v} {P : Cᵒᵖ ⥤ Type max w v}
    (φ : (Functor.const Cᵒᵖ).obj E ⟶ P)
    (hinj : Presheaf.IsLocallyInjective J φ)
    (hsurj : Presheaf.IsLocallySurjective J φ) :
    (constantSheaf J (Type max w v)).obj E ≅ (presheafToSheaf J (Type max w v)).obj P :=
  have := hinj
  have := hsurj
  presheafToSheafObjIso J (Q := (presheafToSheaf J (Type max w v)).obj P)
    (φ ≫ toSheafify J P) inferInstance inferInstance

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

/-! ### The disjoint union of copies of a scheme, and its sheet data -/

section NoSite

variable {V : Scheme.{u}} (ι : Type u)

/-- The fold map of a disjoint union of copies of a scheme is étale: étale morphisms are
Zariski-local at the source and each restriction to a component is an identity. -/
public theorem etale_sigmaDescId : Etale (Sigma.desc fun _ : ι ↦ 𝟙 V) :=
  have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The canonical isomorphism `(∐_{i : ι} V) ×_V V ≅ ∐_{i : ι} V`, the base change of the fold
map along the identity. -/
public def pullbackSigmaDescIdIso :
    pullback (Sigma.desc fun _ : ι ↦ 𝟙 V) (𝟙 V) ≅ ∐ fun _ : ι ↦ V where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) (Sigma.desc fun _ : ι ↦ 𝟙 V) (by
    rw [Category.id_comp, Category.comp_id])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition,
        Category.comp_id]
  inv_hom_id := by rw [pullback.lift_fst]

/-- The isomorphism `pullbackSigmaDescIdIso` is compatible with the fold map, which is the
condition `Stacks.Etale.isSplitOverOfIso` imposes. -/
public theorem pullbackSigmaDescIdIso_hom_comp :
    (pullbackSigmaDescIdIso (V := V) ι).hom ≫ (Sigma.desc fun _ : ι ↦ 𝟙 V) =
      pullback.snd (Sigma.desc fun _ : ι ↦ 𝟙 V) (𝟙 V) := by
  show pullback.fst _ _ ≫ (Sigma.desc fun _ : ι ↦ 𝟙 V) = pullback.snd _ _
  rw [pullback.condition, Category.comp_id]

variable [Finite ι]

/-- **Sheet data for a disjoint union of copies of the base, over the base itself.** The fold map
of `∐_{i : ι} V` becomes a disjoint union of copies of the base after the trivial base change
along the identity of `V`, so it has sheet data over `V`, with index type `ι`. -/
public def isSplitOverSigmaDescId :
    Stacks.Etale.IsSplitOver (Sigma.desc fun _ : ι ↦ 𝟙 V) (𝟙 V) :=
  Stacks.Etale.isSplitOverOfIso _ _ (pullbackSigmaDescIdIso ι)
    (pullbackSigmaDescIdIso_hom_comp ι)

/-- The sheets of `isSplitOverSigmaDescId` are indexed by the index type of the coproduct. -/
public theorem isSplitOverSigmaDescId_I : (isSplitOverSigmaDescId (V := V) ι).I = ι := rfl

/-- The sheets of `isSplitOverSigmaDescId` are the components of the coproduct. -/
public theorem isSplitOverSigmaDescId_sheet (i : ι) :
    (isSplitOverSigmaDescId (V := V) ι).sheet i = Sigma.ι (fun _ : ι ↦ V) i := by
  show Sigma.ι (fun _ : ι ↦ V) i ≫ (pullbackSigmaDescIdIso (V := V) ι).inv ≫
    pullback.fst _ _ = _
  rw [show (pullbackSigmaDescIdIso (V := V) ι).inv ≫ pullback.fst _ _ = 𝟙 _ from
    (pullbackSigmaDescIdIso (V := V) ι).inv_hom_id, Category.comp_id]

end NoSite

section Site

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {V : Scheme.{u}} (hV : B.Contains V)
  (ι : Type u) [Finite ι]

/-- A finite disjoint union of copies of a scheme belonging to a big étale site again belongs to
it: by `AlgebraicGeometry.schemeSize_coproduct_le` its size is bounded by the size of the base,
the index type being finite and hence of cardinality at most `ℵ₀`. -/
public theorem contains_sigmaConst (B : AlgebraicGeometry.BigEtaleSite.{u}) {V : Scheme.{u}}
    (hV : B.Contains V) (ι : Type u) [Finite ι] : B.Contains (∐ fun _ : ι ↦ V) :=
  lt_of_le_of_lt
    (schemeSize_coproduct_le (fun _ : ι ↦ V) V.size (Scheme.aleph0_le_size V)
      (Cardinal.mk_le_aleph0.trans (Scheme.aleph0_le_size V)) fun _ ↦ le_rfl)
    hV

/-- **The split cover.** The disjoint union of `ι` copies of `V`, with its fold map, as an object
of the small étale site of `V`. -/
public def splitObj : SmallEtale B V hV :=
  mkObj B hV (∐ fun _ : ι ↦ V) (Sigma.desc fun _ : ι ↦ 𝟙 V) (contains_sigmaConst B hV ι)
    (etale_sigmaDescId ι)

/-- The underlying scheme of the split cover is the disjoint union. -/
@[simp]
public theorem toScheme_obj_splitObj :
    (SmallEtale.toScheme B V hV).obj (splitObj B hV ι) = ∐ fun _ : ι ↦ V :=
  rfl

/-- The structure morphism of the split cover is the fold map. -/
@[simp]
public theorem hom_splitObj :
    B.inclusion.map (splitObj B hV ι).obj.hom = Sigma.desc fun _ : ι ↦ 𝟙 V :=
  rfl

/-- The structure morphism of the split cover is finite: this is Stacks 0CYI, each component
being an identity. -/
public theorem isFinite_hom_splitObj : IsFinite (B.inclusion.map (splitObj B hV ι).obj.hom) :=
  isFinite_sigmaDesc

/-- A sheet of the split cover, as a morphism of the small étale site out of a given object: the
structure morphism of that object followed by the chosen component of the coproduct. -/
public def splitSheetHom (Z : SmallEtale B V hV) (i : ι) : Z ⟶ splitObj B hV ι :=
  mkHom B hV (B.inclusion.map Z.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) i)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun k ↦ B.inclusion.map Z.obj.hom ≫ k)
        (Sigma.ι_desc (fun _ : ι ↦ 𝟙 V) i)) (Category.comp_id _)))

/-- The underlying morphism of schemes of a sheet morphism. -/
@[simp]
public theorem toScheme_map_splitSheetHom (Z : SmallEtale B V hV) (i : ι) :
    (SmallEtale.toScheme B V hV).map (splitSheetHom B hV ι Z i) =
      B.inclusion.map Z.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) i :=
  rfl

/-! ### The comparison map with the constant presheaf -/

/-- **The comparison map.** The sheets of the split cover define a map from the constant presheaf
on the index type of sheets to the presheaf represented by the split cover: an object of the site
is sent to its structure morphism followed by the chosen sheet. -/
public def constToSplitYoneda :
    (Functor.const (SmallEtale B V hV)ᵒᵖ).obj
        (ULift.{u + 1} ι) ⟶
      uliftYoneda.{u + 1}.obj (splitObj B hV ι) where
  app Z := TypeCat.ofHom fun i ↦ ULift.up (splitSheetHom B hV ι Z.unop i.down)
  naturality Z Z' f := by
    ext i
    refine ULift.ext _ _ (hom_ext B hV ?_)
    have e1 : (SmallEtale.toScheme B V hV).map (splitSheetHom B hV ι Z'.unop i.down)
        = B.inclusion.map Z'.unop.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) i.down := rfl
    have e2 : (SmallEtale.toScheme B V hV).map
          (f.unop ≫ splitSheetHom B hV ι Z.unop i.down)
        = (SmallEtale.toScheme B V hV).map f.unop ≫
          B.inclusion.map Z.unop.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) i.down := by
      rw [Functor.map_comp]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [← Category.assoc, toScheme_map_comp_hom]

/-- The comparison map sends the index of a sheet to the structure morphism followed by that
sheet. -/
@[simp]
public theorem constToSplitYoneda_app (Z : (SmallEtale B V hV)ᵒᵖ)
    (i : ULift.{u + 1} ι) :
    ConcreteCategory.hom ((constToSplitYoneda B hV ι).app Z) i =
      ULift.up (splitSheetHom B hV ι Z.unop i.down) :=
  rfl

/-- The comparison map is locally injective: two distinct sheets agree only over an empty
scheme, and an object of the small étale site with empty underlying scheme is covered by the
empty family. -/
public instance isLocallyInjective_constToSplitYoneda :
    Presheaf.IsLocallyInjective (SmallEtale.topology B V hV) (constToSplitYoneda B hV ι) where
  equalizerSieve_mem {Z} x y hxy := by
    by_cases hij : x.down = y.down
    · rw [show x = y from ULift.ext _ _ hij, Presheaf.equalizerSieve_self_eq_top]
      exact (SmallEtale.topology B V hV).top_mem _
    · have h1 : splitSheetHom B hV ι Z.unop x.down = splitSheetHom B hV ι Z.unop y.down :=
        congrArg ULift.down hxy
      have h2 : B.inclusion.map Z.unop.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) x.down =
          B.inclusion.map Z.unop.obj.hom ≫ Sigma.ι (fun _ : ι ↦ V) y.down :=
        congrArg (SmallEtale.toScheme B V hV).map h1
      exact (SmallEtale.topology B V hV).superset_covering bot_le
        (bot_mem_topology B hV
          ((isSplitOverSigmaDescId (V := V) ι).isEmpty_of_sheet_eq
            (B.inclusion.map Z.unop.obj.hom) hij (by
              rw [isSplitOverSigmaDescId_sheet, isSplitOverSigmaDescId_sheet]
              exact h2)))

/-- The comparison map is locally surjective: a point of the split cover agrees with a sheet on
each member of an open covering of its source, and those members are objects of the small étale
site. -/
public instance isLocallySurjective_constToSplitYoneda :
    Presheaf.IsLocallySurjective (SmallEtale.topology B V hV) (constToSplitYoneda B hV ι) where
  imageSieve_mem {Z} s := by
    obtain ⟨κ, Y, q, hq, idx, hcov, hfac⟩ := (isSplitOverSigmaDescId (V := V) ι).exists_openCover
      (B.inclusion.map Z.obj.hom) ((SmallEtale.toScheme B V hV).map s.down)
      (Eq.trans (toScheme_map_comp_hom B hV s.down) (Category.comp_id _).symm)
    refine (SmallEtale.topology B V hV).superset_covering ?_
      (ofArrows_mem_topology B hV (fun k ↦ openObj B hV Z (q k) (hq k))
        (fun k ↦ openHom B hV Z (q k) (hq k)) fun x ↦ (hcov x).imp fun k hk ↦ hk)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro T f ⟨k⟩
    refine ⟨ULift.up (idx k), ULift.ext _ _ (hom_ext B hV ?_)⟩
    have e1 : (SmallEtale.toScheme B V hV).map
          (splitSheetHom B hV ι (openObj B hV Z (q k) (hq k)) (idx k))
        = (q k ≫ B.inclusion.map Z.obj.hom) ≫ Sigma.ι (fun _ : ι ↦ V) (idx k) := rfl
    have e2 : (SmallEtale.toScheme B V hV).map (openHom B hV Z (q k) (hq k) ≫ s.down)
        = q k ≫ (SmallEtale.toScheme B V hV).map s.down :=
      Eq.trans ((SmallEtale.toScheme B V hV).map_comp _ _)
        (congrArg (fun k' ↦ k' ≫ (SmallEtale.toScheme B V hV).map s.down)
          (toScheme_map_openHom B hV Z (q k) (hq k)))
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [Category.assoc, ← isSplitOverSigmaDescId_sheet ι (idx k)]
    exact (hfac k).symm

/-! ### The constant sheaf is the sheaf represented by the split cover -/

/-- **The representability of a finite constant sheaf.** On the small étale site of `V`, the
constant sheaf on a finite index type `ι` is the sheaf represented by the split cover
`∐_{i : ι} V`.

The constant sheaf is the sheafification of the constant presheaf, and the comparison map
`constToSplitYoneda` from that presheaf to the presheaf represented by the split cover is locally
bijective, so the two sheafifications agree. -/
public def constantSheafIsoSheafifiedYonedaSplitObj :
    (constantSheaf (SmallEtale.topology B V hV) (Type (u + 1))).obj
        (ULift.{u + 1} ι) ≅
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B V hV)).obj (splitObj B hV ι) :=
  Stacks.ConstantSheaf.constantSheafObjIsoSheafification (SmallEtale.topology B V hV)
    (constToSplitYoneda B hV ι) (isLocallyInjective_constToSplitYoneda B hV ι)
    (isLocallySurjective_constToSplitYoneda B hV ι)

/-- **Stacks 03RV for a finite constant sheaf**, which is the base case of the direction that
needs descent. A constant sheaf of sets with finite value on the small étale site of `V` is
represented by an object of that site whose structure morphism is finite — namely by a finite
disjoint union of copies of `V`.

This is the conclusion of Tag 03RV in exactly the form the tag states it; what the general case
adds is the descent of this construction along a trivializing covering. -/
public theorem exists_finiteEtaleRepresentable_constantSheaf (E : Type (u + 1)) [Finite E] :
    ∃ U : SmallEtale B V hV, IsFinite (B.inclusion.map U.obj.hom) ∧
      Nonempty ((constantSheaf (SmallEtale.topology B V hV) (Type (u + 1))).obj E ≅
        (Sheaf.sheafifiedYoneda (SmallEtale.topology B V hV)).obj U) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin E
  refine ⟨splitObj B hV (ULift.{u} (Fin n)), isFinite_hom_splitObj B hV _,
    ⟨?_ ≪≫ constantSheafIsoSheafifiedYonedaSplitObj B hV (ULift.{u} (Fin n))⟩⟩
  exact (constantSheaf (SmallEtale.topology B V hV) (Type (u + 1))).mapIso
    (Equiv.toIso (e.trans (Equiv.ulift.symm.trans Equiv.ulift.symm)))

/-- **Stacks 03RV for a sheaf isomorphic to a finite constant sheaf.** A sheaf of sets on the
small étale site of `V` which is isomorphic to the constant sheaf on a finite set is represented
by an object of the site whose structure morphism is finite. -/
public theorem exists_finiteEtaleRepresentable_of_isConstant
    (F : Sheaf (SmallEtale.topology B V hV) (Type (u + 1)))
    (hF : ∃ E : Type (u + 1), Finite E ∧
      Nonempty ((constantSheaf (SmallEtale.topology B V hV) (Type (u + 1))).obj E ≅ F)) :
    ∃ U : SmallEtale B V hV, IsFinite (B.inclusion.map U.obj.hom) ∧
      Nonempty (F ≅ (Sheaf.sheafifiedYoneda (SmallEtale.topology B V hV)).obj U) := by
  obtain ⟨E, hE, ⟨c⟩⟩ := hF
  have := hE
  obtain ⟨U, hU, ⟨d⟩⟩ := exists_finiteEtaleRepresentable_constantSheaf B hV E
  exact ⟨U, hU, ⟨c.symm ≪≫ d⟩⟩

end Site

end Stacks.EtaleCohomology

end
