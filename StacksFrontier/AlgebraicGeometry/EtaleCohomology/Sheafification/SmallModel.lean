module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.CoveringFamilyPlus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The covering-family plus construction as a presheaf, and sheafification

The covering-family colimit of the previous module is universe-large, so a `Shrink` model is
used as the values of a presheaf. That presheaf is naturally isomorphic to Mathlib's
covering-sieve plus construction, the canonical map out of the original presheaf is the map
defined by the identity covering, and the covering families of an object are directed under
refinement. Together with the existing plus-construction results this gives sheafification.

## Main definitions

* `CategoryTheory.SmallFamilyPlusValue` is the universe-small model of the covering-family
  colimit, and `CategoryTheory.smallFamilyPlusEquiv` its comparison equivalence.
* `CategoryTheory.familyPlusPresheaf` equips the small model with its presheaf structure, and
  `CategoryTheory.familyPlusIso` identifies it with `GrothendieckTopology.plusObj`.
* `CategoryTheory.toSmallFamilyPlus` and `CategoryTheory.toFamilyPlusNatTrans` are the canonical
  maps from the original presheaf.

## Main results

* `CategoryTheory.exists_common_refinement` gives directedness of the covering-family system.
* `CategoryTheory.familyPlusEquiv_mk` specifies the comparison on every matching family, and
  `CategoryTheory.familyPlusPresheaf_map_mk` specifies restriction along every morphism of
  covering families.
* `CategoryTheory.toFamilyPlusNatTrans_app` identifies the canonical map with the
  identity-covering map.
* The existing plus-construction results give separatedness, the sheaf property, injectivity,
  and the sheafification adjunction.

## Implementation notes

Since the type of all covering families of an object is one universe too large, `Shrink`
provides the small model used as the values of `familyPlusPresheaf`. Directedness refers to the
preorder of coverings under existence of a refinement: it is nonempty by `identityCover`, and
any two objects have a common refinement. The transition maps are independent of the refinement
morphism by `PreZeroHypercover.H0.mapOver_eq_of_homOver`. The formula
`familyPlusPresheaf_map_mk` identifies the transported restriction maps with pullback of
matching families; it uses any covering family mapping to the original family over the given
base morphism, so in particular it applies to the fibre-product covering in the source, and is
the pullback-independent description following Sites, Lemma 00W4. The comparison equivalence is
made locally irreducible so that the presheaf functoriality proofs do not unfold it.

## References

* [Stacks Project, Tag 03NS](https://stacks.math.columbia.edu/tag/03NS)
* [Stacks Project, Tag 00W4](https://stacks.math.columbia.edu/tag/00W4)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type u) (U : C)

section SmallModel

attribute [local irreducible] familyPlusEquiv

/-- A universe-small model of the covering-family colimit. -/
def SmallFamilyPlusValue := Shrink.{u} (FamilyPlusValue J F U)

/-- The comparison equivalence on the universe-small model. -/
noncomputable def smallFamilyPlusEquiv :
    SmallFamilyPlusValue J F U ≃ (J.plusObj F).obj (op U) :=
  (Equiv.refl _).trans <|
    (equivShrink (FamilyPlusValue J F U)).symm.trans (familyPlusEquiv J F U)

private theorem smallFamilyPlusEquiv_equivShrink_mk
    (x : FamilyPlusValue J F U) :
    smallFamilyPlusEquiv J F U (equivShrink (FamilyPlusValue J F U) x) =
      familyPlusEquiv J F U x := by
  change familyPlusEquiv J F U
    ((equivShrink (FamilyPlusValue J F U)).symm
      (equivShrink (FamilyPlusValue J F U) x)) = familyPlusEquiv J F U x
  rw [Equiv.symm_apply_apply]

/-- The presheaf whose values are the covering-family colimits of zeroth Čech cohomology. -/
@[stacks 03NS "part (1), the presheaf"]
noncomputable def familyPlusPresheaf : Cᵒᵖ ⥤ Type u where
  obj X := SmallFamilyPlusValue J F X.unop
  map {X Y} f := ↾ fun x => (smallFamilyPlusEquiv J F Y.unop).symm
    ((J.plusObj F).map f (smallFamilyPlusEquiv J F X.unop x))
  map_id X := by
    ext x
    apply (smallFamilyPlusEquiv J F X.unop).injective
    simp
  map_comp f g := by
    ext x
    apply (smallFamilyPlusEquiv J F _).injective
    simp

/-- The comparison equivalence commutes with restriction maps, pointwise. -/
private theorem smallFamilyPlusEquiv_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SmallFamilyPlusValue J F X.unop) :
    smallFamilyPlusEquiv J F Y.unop ((familyPlusPresheaf J F).map f x) =
      (J.plusObj F).map f (smallFamilyPlusEquiv J F X.unop x) :=
  Equiv.apply_symm_apply _ _

/-- On every representative, the comparison sends a matching family to the same matching
family on the generated covering sieve, and then to its colimit class. This characterizes the
comparison independently of any choices made in extending a family to its generated sieve. -/
@[stacks 03NS "part (1), comparison on representatives"]
theorem familyPlusEquiv_mk
    (E : J.toPrecoverage.ZeroHypercover.{u} U)
    (s : PreZeroHypercover.H0 F E.toPreZeroHypercover) :
    familyPlusEquiv J F U
        (Quotient.mk (Relation.EqvGen.setoid (FamilyPlusRelated J F U)) ⟨E, s⟩) =
      GrothendieckTopology.Plus.mk (familyMatchingFamily J F U E s) := by
  simp [familyPlusEquiv, Equiv.ofBijective, Quotient.lift_mk]

/-- Restriction is induced by pulling back matching families. Any morphism of covering
families over the base morphism computes the same restriction; thus this includes the
canonical fibre-product covering without requiring a choice of fibre products. -/
@[stacks 03NS "part (1), restriction on representatives"]
theorem familyPlusPresheaf_map_mk {V : C} (f : V ⟶ U)
    (E : J.toPrecoverage.ZeroHypercover.{u} U)
    (G : J.toPrecoverage.ZeroHypercover.{u} V)
    (φ : G.toPreZeroHypercover.HomOver E.toPreZeroHypercover f)
    (s : PreZeroHypercover.H0 F E.toPreZeroHypercover) :
    (familyPlusPresheaf J F).map f.op
        (equivShrink (FamilyPlusValue J F U)
          (Quotient.mk (Relation.EqvGen.setoid (FamilyPlusRelated J F U)) ⟨E, s⟩)) =
      equivShrink (FamilyPlusValue J F V)
        (Quotient.mk (Relation.EqvGen.setoid (FamilyPlusRelated J F V))
          ⟨G, PreZeroHypercover.H0.mapOver F φ s⟩) := by
  apply (smallFamilyPlusEquiv J F V).injective
  refine (smallFamilyPlusEquiv_map J F f.op _).trans ?_
  rw [smallFamilyPlusEquiv_equivShrink_mk (J := J) (F := F) (U := V),
    smallFamilyPlusEquiv_equivShrink_mk (J := J) (F := F) (U := U), familyPlusEquiv_mk,
    familyPlusEquiv_mk, GrothendieckTopology.Plus.res_mk_eq_mk_pullback]
  apply (GrothendieckTopology.Plus.eq_mk_iff_exists
    ((familyMatchingFamily J F U E s).pullback f)
    (familyMatchingFamily J F V G (PreZeroHypercover.H0.mapOver F φ s))).2
  refine ⟨familyCover J V G,
    coverHomOfHomOverBase (J := J) (U := U) f φ, 𝟙 _, ?_⟩
  rw [familyMatchingFamily_pullback_refine (J := J) (F := F) (U := U) f φ s]
  rfl

private lemma plus_mk_identityCover (x : F.obj (op U)) :
    GrothendieckTopology.Plus.mk (Meq.mk (J := J) ⊤ x) =
      GrothendieckTopology.Plus.mk
        (familyMatchingFamily J F U (identityCover J U) (identityH0 J F U x)) := by
  let E := identityCover J U
  let h : (⊤ : J.Cover U) ⟶ familyCover J U E := homOfLE (fun V f hf => by
    apply (Sieve.mem_ofArrows_iff E.toPreZeroHypercover.X E.toPreZeroHypercover.f f).2
    refine ⟨PUnit.unit, f, ?_⟩
    change f = f ≫ 𝟙 U
    simp)
  apply (GrothendieckTopology.Plus.eq_mk_iff_exists
    (Meq.mk (J := J) ⊤ x)
    (familyMatchingFamily J F U E (identityH0 J F U x))).2
  refine ⟨⊤, 𝟙 _, h, ?_⟩
  apply Meq.ext
  intro I
  rw [Meq.refine_apply, Meq.refine_apply]
  change F.map I.f.op x =
    familyMatchingFamily J F U E (identityH0 J F U x)
      ⟨I.Y, I.f, (leOfHom h) _ I.hf⟩
  have heq : I.f = I.f ≫ E.toPreZeroHypercover.f PUnit.unit := by
    change I.f = I.f ≫ 𝟙 U
    simp
  rw [Meq.congr_apply _ heq ((leOfHom h) _ I.hf)]
  have hid : (identityH0 J F U x).1 PUnit.unit = x := by
    dsimp [identityH0, identityCover, Precoverage.ZeroHypercover.singleton]
    change F.map (𝟙 (op U)) x = x
    exact F.map_id_apply _ _
  exact (congrArg (F.map I.f.op) hid.symm).trans (familyMatchingFamily_factor (J := J) (F := F)
    (U := U) E (identityH0 J F U x) PUnit.unit I.f).symm

/-- Covering families form a directed system under refinement. -/
@[stacks 03NS "part (1), directedness"]
theorem exists_common_refinement
    (E G : J.toPrecoverage.ZeroHypercover.{u} U) :
    ∃ H : J.toPrecoverage.ZeroHypercover.{u} U,
      Nonempty (H.toPreZeroHypercover.Hom E.toPreZeroHypercover) ∧
        Nonempty (H.toPreZeroHypercover.Hom G.toPreZeroHypercover) := by
  let W : Sieve U := (familyCover J U E : Sieve U) ⊓ (familyCover J U G : Sieve U)
  have hW : W ∈ J U := J.intersection_covering (familyCover J U E).2 (familyCover J U G).2
  let H : J.toPrecoverage.ZeroHypercover.{u} U :=
    ⟨W.arrows.preZeroHypercover, by
      simpa using (GrothendieckTopology.arrows_mem_toPrecoverage_iff J W).2 hW⟩
  have hWE : W ≤ E.toPreZeroHypercover.sieve₀ := inf_le_left
  have hWG : W ≤ G.toPreZeroHypercover.sieve₀ := inf_le_right
  have hmem (i : H.toPreZeroHypercover.I₀) : W (H.toPreZeroHypercover.f i) := i.2
  let witnessesE (i : H.toPreZeroHypercover.I₀) :=
    (Sieve.mem_ofArrows_iff E.toPreZeroHypercover.X E.toPreZeroHypercover.f _).1
      (hWE _ (hmem i))
  choose jE aE haE using witnessesE
  let φ : H.toPreZeroHypercover.HomOver E.toPreZeroHypercover (𝟙 U) :=
    ⟨jE, aE, fun i => by simpa using (haE i).symm⟩
  let witnessesG (i : H.toPreZeroHypercover.I₀) :=
    (Sieve.mem_ofArrows_iff G.toPreZeroHypercover.X G.toPreZeroHypercover.f _).1
      (hWG _ (hmem i))
  choose jG aG haG using witnessesG
  let ψ : H.toPreZeroHypercover.HomOver G.toPreZeroHypercover (𝟙 U) :=
    ⟨jG, aG, fun i => by simpa using (haG i).symm⟩
  exact ⟨H, ⟨PreZeroHypercover.homOverIdEquivHom _ _ φ⟩,
    ⟨PreZeroHypercover.homOverIdEquivHom _ _ ψ⟩⟩

/-- The comparison commutes with restriction maps. -/
@[stacks 03NS "part (1), naturality of the comparison"]
theorem smallFamilyPlusEquiv_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (familyPlusPresheaf J F).map f ≫ (smallFamilyPlusEquiv J F Y.unop).toIso.hom =
      (smallFamilyPlusEquiv J F X.unop).toIso.hom ≫ (J.plusObj F).map f := by
  ext x
  exact smallFamilyPlusEquiv_map J F f x

/-- The covering-family plus presheaf is naturally isomorphic to the covering-sieve plus
presheaf. -/
noncomputable def familyPlusIso : familyPlusPresheaf J F ≅ J.plusObj F :=
  NatIso.ofComponents (fun X ↦ (smallFamilyPlusEquiv J F X.unop).toIso)
    (fun f ↦ smallFamilyPlusEquiv_naturality J F f)

/-- The canonical map into the small covering-family colimit. -/
noncomputable def toSmallFamilyPlus (x : F.obj (op U)) : SmallFamilyPlusValue J F U :=
  equivShrink (FamilyPlusValue J F U) (toFamilyPlus J F U x)

/-- The canonical map of presheaves into the covering-family plus construction. -/
@[sga "4 II 3.0.5" "special case"]
noncomputable def toFamilyPlusNatTrans : F ⟶ familyPlusPresheaf J F :=
  J.toPlus F ≫ (familyPlusIso J F).inv

end SmallModel

/-- The canonical presheaf map is pointwise the map defined by the identity covering. -/
@[stacks 03NS "part (2), the canonical map"]
theorem toFamilyPlusNatTrans_app (x : F.obj (op U)) :
    (toFamilyPlusNatTrans J F).app (op U) x = toSmallFamilyPlus J F U x := by
  apply (smallFamilyPlusEquiv J F U).injective
  change (smallFamilyPlusEquiv J F U)
      ((smallFamilyPlusEquiv J F U).symm ((J.toPlus F).app (op U) x)) =
    (smallFamilyPlusEquiv J F U)
      (equivShrink (FamilyPlusValue J F U) (toFamilyPlus J F U x))
  simp only [Equiv.apply_symm_apply]
  rw [smallFamilyPlusEquiv_equivShrink_mk, toFamilyPlus, familyPlusEquiv_mk,
    GrothendieckTopology.Plus.toPlus_eq_mk]
  exact plus_mk_identityCover (J := J) (F := F) (U := U) x

end CategoryTheory

add_to_stacks 03NS "part (1), the covering-sieve presheaf"
  CategoryTheory.GrothendieckTopology.plusObj
add_to_stacks 03NS "part (2), the canonical natural transformation"
  CategoryTheory.GrothendieckTopology.toPlusNatTrans
add_to_sga "4 II 3.0.5" CategoryTheory.GrothendieckTopology.toPlusNatTrans
add_to_stacks 03NS "part (3), the sheaf property" StacksSheafification.isSheaf_plusObj
add_to_stacks 03NS "part (3), injectivity" StacksSheafification.injective_toPlus_app
add_to_stacks 03NS "part (4)" StacksSheafification.isSeparated_plusObj
add_to_stacks 03NS "part (5), the sheaf property"
  StacksSheafification.isSheaf_plusObj_plusObj
add_to_stacks 03NS "part (5), the functorial universal property"
  CategoryTheory.plusPlusAdjunction
add_to_sga "3 IV 4.3.14" "more general" CategoryTheory.plusPlusAdjunction
add_to_sga "3 IV 4.3.16" "more general" CategoryTheory.plusPlusAdjunction
add_to_sga "4 II 3.4" CategoryTheory.plusPlusAdjunction
add_to_sga "4 II 6.4" CategoryTheory.plusPlusAdjunction
