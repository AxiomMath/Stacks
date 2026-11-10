module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Jacobson
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Translation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Varieties.ClosedPointResidue
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.AlgClosureSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GaloisBaseChangeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves

/-!
# A separated group algebraic space over a field becomes a scheme over an algebraic closure

Let `G` be a group algebraic space over a field `k` which is separated. Then the base change of
`G` to an algebraic closure of `k` is a scheme (Stacks 0B8E).

The source argues over a large algebraically closed extension `K/k` and then descends to `k̄` with
Stacks 0B84. Over `K`, choose an étale atlas `U ⟶ G`; for `#K` larger than `U`, the base change
`U_K` is a Jacobson scheme whose closed points are `K`-rational (Stacks 0479). The schematic locus
of `G_K` is open and nonempty, since `G` is decent and so its own schematic locus is dense
(Stacks 06NH); its preimage in `U_K` therefore contains a closed point, which gives a `K`-rational
point of `G_K` in the schematic locus. Translations of `G_K` by `K`-rational points are
automorphisms, so they preserve the schematic locus and move that point onto any other: every
`K`-rational point of `G_K` is schematic. Every closed point of `U_K` maps to such a point, so the
preimage of the schematic locus is an open set containing all closed points of a Jacobson space,
that is all of `U_K`, and `G_K` is a scheme.

## Main results

* `GroupOverField.all_groupSections_factor_of_one` and
  `GroupOverField.graph_factors_schematicLocus`: if one section of a group algebraic space over a
  base factors through the schematic locus, then every section does.
* `GroupOverField.exists_cardinal_mem_schematicLocus_prod`: over every large enough algebraically
  closed extension `L/k` in the site, every point of `h_{Spec L} × G` is in the schematic locus.
* `GroupOverField.exists_isAlgClosed_isRepresentable_relocalizeRestrict`: `G_L` is a scheme for
  some algebraically closed extension `L/k`.
* `GroupOverField.isRepresentable_relocalizeRestrict_algebraicClosure_of_isSeparatedOver`:
  Stacks 0B8E, `G_{k̄}` is a scheme.

## Implementation notes

The large-field half is phrased in the site of `S ≅ Spec k`, with the base change written as the
product `h_{Spec L} × G`, so that the translations are those of
`AlgebraicGeometry.Space.GroupOverField.leftTrans` and no change of site is involved. Stacks 02W6
(`CategoryTheory.isRepresentable_overMap_iff`) turns representability of that product into
representability of the restriction of `G` to the big fppf site of `Spec L`, the form Stacks 0B84
part (1) consumes and produces. The site contains fields of every cardinality below its cutoff,
which is a strong limit, so the bound of Stacks 0479, the size of the chart, can be exceeded
inside the site.

Separatedness enters twice: through decency, for the density of the schematic locus, and through
quasi-separatedness, which is the hypothesis of Stacks 0B84. Separatedness is the relative notion
`AlgebraicGeometry.Space.IsSeparatedOver`, which over the affine `Spec k` agrees with absolute
separatedness.

## References

* [Stacks Project, Tag 0B8E](https://stacks.math.columbia.edu/tag/0B8E)
* [Stacks Project, Tag 0B84](https://stacks.math.columbia.edu/tag/0B84)
* [Stacks Project, Tag 0479](https://stacks.math.columbia.edu/tag/0479)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Cardinal

universe u

namespace AlgebraicGeometry.Space.GroupOverField

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An automorphism preserves the schematic locus.** The image of the schematic locus of an
algebraic space under an automorphism of it is again contained in the schematic locus: the image
is an open subspace isomorphic to the schematic locus, hence representable, and the schematic
locus contains every representable open subspace. -/
private theorem schematicLocus_image_le
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) (e : F ≅ F) :
    Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom) ≤ schematicLocus B S hS F := by
  obtain ⟨hZopen, hZrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF
  let : (schematicLocus B S hS F).toFunctor.IsRepresentable := hZrep
  have : Mono ((schematicLocus B S hS F).ι ≫ e.hom) :=
    @mono_comp _ _ _ _ _ _ (by infer_instance : Mono (schematicLocus B S hS F).ι) _
      (IsIso.mono_of_iso e.hom)
  -- the image is isomorphic to the schematic locus, hence an algebraic space and representable
  have βiso : (schematicLocus B S hS F).toFunctor ≅
      (Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom)).toFunctor :=
    asIso (Subfunctor.toRange ((schematicLocus B S hS F).ι ≫ e.hom))
  have hVrep :
      (Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom)).toFunctor.IsRepresentable :=
    isRepresentable_of_natIso (schematicLocus B S hS F).toFunctor βiso
  have hVAlg : IsAlgebraicSpace B S hS
      (Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom)).toFunctor :=
    isAlgebraicSpace_of_iso B S hS βiso hZopen.1
  -- the inclusion of the image is an open immersion, being the inverse iso followed by `p`
  have hVOpen : IsOpenImmersion B S hS
      (Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom)).ι := by
    have hpOpen : IsOpenImmersion B S hS ((schematicLocus B S hS F).ι ≫ e.hom) :=
      MorphismProperty.RespectsIso.postcomp _ e.hom _ hZopen.2
    have hcomp :
        (asIso (Subfunctor.toRange ((schematicLocus B S hS F).ι ≫ e.hom))).inv ≫
            ((schematicLocus B S hS F).ι ≫ e.hom) =
          (Subfunctor.range ((schematicLocus B S hS F).ι ≫ e.hom)).ι :=
      (Iso.inv_comp_eq _).2
        (Subfunctor.toRange_ι ((schematicLocus B S hS F).ι ≫ e.hom)).symm
    exact hcomp ▸ MorphismProperty.RespectsIso.precomp _ _ _ hpOpen
  exact le_schematicLocus B S hS F _ ⟨hVAlg, hVOpen⟩ hVrep

variable (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A translation carries the schematic locus into itself.** If a section `q` of a group
algebraic space over `Y` factors through the schematic locus, then so does its right translate
by any section `p`. -/
private theorem groupTranslation_factors_schematicLocus
    (A : Grp (Over Y)) (hA : IsAlgebraicSpace B S hS A.X.left) (p q : 𝟙_ (Over Y) ⟶ A.X)
    (hq : ∃ z : (𝟙_ (Over Y)).left ⟶ (schematicLocus B S hS A.X.left).toFunctor,
      z ≫ (schematicLocus B S hS A.X.left).ι = q.left) :
    ∃ z : (𝟙_ (Over Y)).left ⟶ (schematicLocus B S hS A.X.left).toFunctor,
      z ≫ (schematicLocus B S hS A.X.left).ι =
        (q ≫ (GrpObj.mulRight (A := A.X) p).hom).left := by
  obtain ⟨z, hz⟩ := hq
  have hle : Subfunctor.range ((schematicLocus B S hS A.X.left).ι ≫
      ((Over.forget Y).mapIso (GrpObj.mulRight (A := A.X) p)).hom) ≤
        schematicLocus B S hS A.X.left :=
    schematicLocus_image_le B S hS A.X.left hA ((Over.forget Y).mapIso
      (GrpObj.mulRight (A := A.X) p))
  refine ⟨z ≫ Subfunctor.lift _ hle, ?_⟩
  rw [Category.assoc, Subfunctor.lift_ι]
  exact congrArg (fun f => f ≫ ((Over.forget Y).mapIso
    (GrpObj.mulRight (A := A.X) p)).hom) hz

set_option synthInstance.maxHeartbeats 100000 in
-- instance search for the group-object and cartesian monoidal structures on `Over Y`
/-- **The schematic locus is translation-invariant on sections.** If some section `q` of a group
algebraic space over `Y` factors through the schematic locus, then every section `p` does: `p` is
the right translate of the identity section by `p`, and the identity section is the right
translate of `q` by `q⁻¹`. -/
theorem all_groupSections_factor_of_one
    (A : Grp (Over Y)) (hA : IsAlgebraicSpace B S hS A.X.left) (q : 𝟙_ (Over Y) ⟶ A.X)
    (hq : ∃ z : (𝟙_ (Over Y)).left ⟶ (schematicLocus B S hS A.X.left).toFunctor,
      z ≫ (schematicLocus B S hS A.X.left).ι = q.left)
    (p : 𝟙_ (Over Y) ⟶ A.X) :
    ∃ z : (𝟙_ (Over Y)).left ⟶ (schematicLocus B S hS A.X.left).toFunctor,
      z ≫ (schematicLocus B S hS A.X.left).ι = p.left := by
  -- first translate `q` to the identity section, then the identity section to `p`
  have hone := groupTranslation_factors_schematicLocus B S hS Y A hA (q ≫ GrpObj.inv) q hq
  have heq : q ≫ (GrpObj.mulRight (A := A.X) (q ≫ GrpObj.inv)).hom =
      MonObj.one (X := A.X) := by
    simp only [GrpObj.mulRight, comp_lift_assoc, Category.comp_id,
      ← Category.assoc q (toUnit _)]
    rw [show q ≫ toUnit A.X = 𝟙 _ from toUnit_unique _ _, Category.id_comp,
      GrpObj.lift_comp_inv_right]
    simp
  rw [heq] at hone
  have hp := groupTranslation_factors_schematicLocus B S hS Y A hA p
    (MonObj.one (X := A.X)) hone
  have hpeq : (MonObj.one (X := A.X)) ≫ (GrpObj.mulRight (A := A.X) p).hom = p := by
    simp only [GrpObj.mulRight, comp_lift_assoc, Category.comp_id,
      ← Category.assoc (MonObj.one (X := A.X)) (toUnit _)]
    rw [show (MonObj.one (X := A.X)) ≫ toUnit A.X = 𝟙 _ from toUnit_unique _ _,
      Category.id_comp]
    have h := MonObj.lift_comp_one_left (A := 𝟙_ (Over Y)) (B := A.X) (𝟙 (𝟙_ (Over Y))) p
    rw [Category.id_comp] at h
    exact h
  rwa [hpeq] at hp

/-- **A large algebraically closed extension inside the site.** For every cardinal `κ` below the
cutoff of a big fppf site containing `Spec k`, there is an algebraically closed extension `K/k`
of cardinality exceeding `κ` whose spectrum is still an object of the site.

The witness is the algebraic closure of the purely transcendental extension of `k` on
`Order.succ (max κ (max #k ℵ₀))` many variables. That many variables make the field larger than
`κ`, while the cutoff is a strong prelimit, so the successor stays below it; and passing to the
algebraic closure does not increase the cardinality of an infinite field, by
`Algebra.IsAlgebraic.cardinalMk_le_max`, so the size of the spectrum stays below the cutoff. -/
private theorem exists_large_algClosed_contained
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (κ : Cardinal.{u}) (hκ : κ < B.cutoff) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K)
      (_ : B.Contains (Spec (.of K))), κ < Cardinal.mk K := by
  classical
  have hkcard : Cardinal.mk k < B.cutoff := by
    have h : (Spec (CommRingCat.of k)).size < B.cutoff := hk
    rw [AlgebraicGeometry.Scheme.size_Spec] at h
    exact lt_of_le_of_lt (le_max_right ℵ₀ (Cardinal.mk k)) h
  -- a cardinal above `κ`, above `#k`, and infinite, together with its successor
  let bound : Cardinal.{u} := max κ (max (Cardinal.mk k) ℵ₀)
  let κplus : Cardinal.{u} := Order.succ bound
  have hkbound : Cardinal.mk k ≤ bound :=
    le_trans (le_max_left (Cardinal.mk k) ℵ₀) (le_max_right κ _)
  have hwbound : ℵ₀ ≤ bound :=
    le_trans (le_max_right (Cardinal.mk k) ℵ₀) (le_max_right κ _)
  have hbound : bound < B.cutoff :=
    max_lt hκ (max_lt hkcard B.aleph0_lt_cutoff)
  have hsucclt : κplus < B.cutoff :=
    B.cutoff_isStrongPrelimit.isSuccPrelimit.succ_lt hbound
  -- the variable set, of that successor cardinality
  let α : Type u := Quotient.out κplus
  have hα : Cardinal.mk α = κplus := Cardinal.mk_out κplus
  have : Infinite α :=
    Cardinal.infinite_iff.mpr ((hwbound.trans (Order.le_succ bound)).trans_eq hα.symm)
  -- the purely transcendental extension
  let K₀ : Type u := FractionRing (MvPolynomial α k)
  have hK₀card : Cardinal.mk K₀ = κplus := by
    have h₁ : Cardinal.mk K₀ = max (max (Cardinal.mk k) (Cardinal.mk α)) ℵ₀ := by
      change Cardinal.mk (FractionRing (MvPolynomial α k)) = _
      rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max_lift]
      simp only [Cardinal.lift_id]
    rw [h₁, hα, max_eq_right (le_trans hkbound (Order.le_succ bound)),
      max_eq_left (le_trans hwbound (Order.le_succ bound))]
  have hK₀inf : ℵ₀ ≤ Cardinal.mk K₀ :=
    (hwbound.trans (Order.le_succ bound)).trans_eq hK₀card.symm
  -- its algebraic closure has the same cardinality, `K₀` being infinite
  let L : Type u := AlgebraicClosure K₀
  have hLle : Cardinal.mk L ≤ Cardinal.mk K₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K₀ L).trans_eq (max_eq_left hK₀inf)
  have hLcontained : B.Contains (Spec (.of L)) := by
    change (Spec (CommRingCat.of L)).size < B.cutoff
    rw [AlgebraicGeometry.Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (hLle.trans_lt (hK₀card.trans_lt hsucclt))
  let : Algebra k L := ((algebraMap K₀ L).comp (algebraMap k K₀)).toAlgebra
  refine ⟨L, inferInstance, inferInstance, inferInstance, hLcontained, ?_⟩
  calc κ ≤ bound := le_max_left _ _
    _ < κplus := Order.lt_succ bound
    _ = Cardinal.mk K₀ := hK₀card.symm
    _ ≤ Cardinal.mk L := Cardinal.mk_le_of_injective (algebraMap K₀ L).injective

/-! ### Sections of a base change -/

section Sections

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
variable (G : GroupAlgebraicSpace C S hS (yoneda.obj (⊤_ (BigFppfOver C S hS)))
  (isAlgebraicSpace_yoneda C S hS _))

/-- **The schematic locus of a base change contains all sections or none.** Let `G` be a group
algebraic space over the terminal presheaf and `E` an object of the site. If the section
`(id, t')` of `h_E × G ⟶ h_E` factors through the schematic locus of `h_E × G`, then so does the
section `(id, t)` for every `t : h_E ⟶ G`: the left translation by `t · t'⁻¹` is an automorphism
of `h_E × G`, it carries the first section to the second, and automorphisms preserve the
schematic locus. -/
theorem graph_factors_schematicLocus {E : BigFppfOver C S hS}
    (t t' : yoneda.obj E ⟶ G.obj.X.left)
    (ht' : ∃ z : yoneda.obj E ⟶ (schematicLocus C S hS (yoneda.obj E ⨯ G.obj.X.left)).toFunctor,
      z ≫ (schematicLocus C S hS (yoneda.obj E ⨯ G.obj.X.left)).ι = prod.lift (𝟙 _) t') :
    ∃ z : yoneda.obj E ⟶ (schematicLocus C S hS (yoneda.obj E ⨯ G.obj.X.left)).toFunctor,
      z ≫ (schematicLocus C S hS (yoneda.obj E ⨯ G.obj.X.left)).ι = prod.lift (𝟙 _) t := by
  obtain ⟨z, hz⟩ := ht'
  have hle := schematicLocus_image_le C S hS _ (isAlgebraicSpace_prod_yoneda_obj E G.property)
    (leftTrans G (t * t'⁻¹))
  refine ⟨z ≫ Subfunctor.lift _ hle, ?_⟩
  rw [Category.assoc, Subfunctor.lift_ι, ← Category.assoc, hz, comp_leftTrans_hom]
  simp only [prod.lift_fst_assoc, Category.id_comp, prod.lift_snd, inv_mul_cancel_right,
    prod.lift_fst]

end Sections

/-! ### Over a large algebraically closed field every point is schematic -/

section LargeField

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {k : Type u} [Field k]
  (e : S ≅ Spec (.of k))
variable (G : GroupAlgebraicSpace C S hS (yoneda.obj (⊤_ (BigFppfOver C S hS)))
  (isAlgebraicSpace_yoneda C S hS _))

/-- **A closed point with algebraic residue field over an algebraically closed field is a
rational section.** Let `L` be algebraically closed and `f : X ⟶ Spec L`. If the residue field
of `x` is algebraic over `L`, then the structure map `L → κ(x)` is an isomorphism and the
canonical morphism `Spec κ(x) ⟶ X` becomes a section of `f` through `x`. -/
theorem exists_section_of_isAlgebraic_residueField
    (L : Type u) [Field L] [IsAlgClosed L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of L)) (x : X)
    (hx : letI : (f x).asIdeal.IsPrime := (f x).isPrime
      letI := ((CommRingCat.ofHom (algebraMap L (f x).asIdeal.ResidueField)) ≫
        (Scheme.Spec.residueFieldIso (.of L) (f x)).inv ≫
        f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic L (X.residueField x)) :
    ∃ a : Spec (.of L) ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ t, a t = x := by
  let : (f x).asIdeal.IsPrime := (f x).isPrime
  let ρ : CommRingCat.of L ⟶ X.residueField x :=
    CommRingCat.ofHom (algebraMap L (f x).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso (.of L) (f x)).inv ≫ f.residueFieldMap x
  let : Algebra L (X.residueField x) := ρ.hom.toAlgebra
  have : Algebra.IsAlgebraic L (X.residueField x) := hx
  have : Algebra.IsIntegral L (X.residueField x) :=
    Algebra.isAlgebraic_iff_isIntegral.mp hx
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L))
  have hρ : Spec.map ρ = X.fromSpecResidueField x ≫ f := by
    simp only [ρ, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    exact f.SpecMap_residueFieldMap_fromSpecResidueField x
  refine ⟨Spec.map (inv ρ) ≫ X.fromSpecResidueField x, ?_,
    fun t => Scheme.fromSpecResidueField_apply x _⟩
  rw [Category.assoc, ← hρ, ← Spec.map_comp]
  simp

/-- **Sections of `U ×_k Spec L` give sections of the site product.** For an object `U` of the
site over `S ≅ Spec k` and an extension `L/k`, the scheme `U ×_k Spec L` maps surjectively onto
the scheme of the site product `Spec L ⨯ U`, and every section of `U ×_k Spec L ⟶ Spec L` is
carried to the section `(id, τ)` of the site product for some `τ : Spec L ⟶ U`. -/
private theorem exists_surjective_pullback_toScheme_prod_extObj (U : BigFppfOver C S hS)
    (L : Type u) [Field L] [Algebra k L] (hL : C.Contains (Spec (.of L))) :
    ∃ ψ : pullback ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U) ≫ e.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
        (BigFppfOver.toScheme C S hS).obj (extObj C S hS e L hL ⨯ U),
      Function.Surjective ψ ∧
      ∀ a : Spec (.of L) ⟶ pullback
        ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U) ≫ e.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap k L))),
        a ≫ pullback.snd _ _ = 𝟙 _ → ∃ τ : extObj C S hS e L hL ⟶ U,
          (BigFppfOver.toScheme C S hS).map (prod.lift (𝟙 _) τ) = a ≫ ψ := by
  let E := extObj C S hS e L hL
  let sU : (BigFppfOver.toScheme C S hS).obj U ⟶ S :=
    (BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U)
  let f : (BigFppfOver.toScheme C S hS).obj U ⟶ Spec (.of k) := sU ≫ e.hom
  let φL : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback ((BigFppfOver.toScheme C S hS).map (prod.fst : E ⨯ U ⟶ E))
      ((BigFppfOver.toScheme C S hS).map (prod.snd : E ⨯ U ⟶ U))
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from E))
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U)) :=
    (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd E U)
      Over.mkIdTerminal).map (BigFppfOver.toScheme C S hS)
  have hsE : (BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from E) ≫ e.hom = φL := by
    rw [toScheme_map_from_extObj]
    simp [φL]
  let ψ : pullback f φL ⟶ (BigFppfOver.toScheme C S hS).obj (E ⨯ U) :=
    hpb.lift (pullback.snd f φL) (pullback.fst f φL) (by
      rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hsE]
      exact pullback.condition.symm)
  let θ : (BigFppfOver.toScheme C S hS).obj (E ⨯ U) ⟶ pullback f φL :=
    pullback.lift ((BigFppfOver.toScheme C S hS).map prod.snd)
      ((BigFppfOver.toScheme C S hS).map prod.fst) (by
        rw [← hsE, ← Category.assoc, ← hpb.w]
        simp)
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    apply hpb.hom_ext
    · simp only [θ, ψ, Category.assoc, IsPullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [θ, ψ, Category.assoc, IsPullback.lift_snd, pullback.lift_fst, Category.id_comp]
  have hU : U.hom.hom = sU := by
    change _ = C.inclusion.map (Over.mkIdTerminal.from U).left
    rw [Over.mkIdTerminal_from_left]
    rfl
  refine ⟨ψ, fun t => ⟨θ t, by
    rw [← Scheme.Hom.comp_apply, hθψ]
    rfl⟩, fun a ha => ?_⟩
  let τ : E ⟶ U := Over.homMk ⟨a ≫ pullback.fst f φL⟩ (by
    apply ObjectProperty.hom_ext
    change (a ≫ pullback.fst f φL) ≫ U.hom.hom = φL ≫ e.inv
    rw [hU, ← cancel_mono e.hom, Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    change a ≫ pullback.fst f φL ≫ f = φL
    rw [pullback.condition, ← Category.assoc, ha, Category.id_comp])
  refine ⟨τ, ?_⟩
  apply hpb.hom_ext
  · rw [← Functor.map_comp, prod.lift_fst, CategoryTheory.Functor.map_id, Category.assoc,
      IsPullback.lift_fst, ha]
    rfl
  · rw [← Functor.map_comp, prod.lift_snd, Category.assoc, IsPullback.lift_snd]
    rfl

/-- **A section of the chart lands on a graph point.** Let `q : h_U ⟶ F` and let `ψ` map a
scheme `T` to the scheme of the site product `Spec L ⨯ U`. If a section `a` through `t` composes
with `ψ` to the section `(id, τ)`, then the point of `h_{Spec L} × F` given by `ψ t` is the class
of the graph of `τ` followed by `q`. -/
private theorem pointsMap_symm_eq_class_ptOf_prod_lift {U : BigFppfOver C S hS}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (q : yoneda.obj U ⟶ F) (L : Type u) [Field L]
    [Algebra k L] (hL : C.Contains (Spec (.of L))) {T : Scheme.{u}}
    (ψ : T ⟶ (BigFppfOver.toScheme C S hS).obj (extObj C S hS e L hL ⨯ U))
    (a : Spec (.of L) ⟶ T) (t : T) (hat : ∀ s, a s = t) (τ : extObj C S hS e L hL ⟶ U)
    (hτ : (BigFppfOver.toScheme C S hS).map (prod.lift (𝟙 _) τ) = a ≫ ψ) :
    pointsMap C S hS _ ((yonedaProdIso C S hS _ U).hom ≫ prod.map (𝟙 _) q)
        ((schemePointsHomeomorph C S hS _).symm (ψ t)) =
      (ptOf C S hS e _ L hL (prod.lift (𝟙 _) (yoneda.map τ ≫ q))).class C S hS _ := by
  let E := extObj C S hS e L hL
  let qL : yoneda.obj (E ⨯ U) ⟶ yoneda.obj E ⨯ F :=
    (yonedaProdIso C S hS E U).hom ≫ prod.map (𝟙 _) q
  let σ : E ⟶ E ⨯ U := prod.lift (𝟙 E) τ
  have hs : yoneda.map σ ≫ qL = prod.lift (𝟙 _) (yoneda.map τ ≫ q) := by
    apply prod.hom_ext
    · simp only [qL, σ, Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst,
        yonedaProdIso_hom_fst]
      rw [← Functor.map_comp, prod.lift_fst, CategoryTheory.Functor.map_id]
    · simp only [qL, σ, Category.assoc, prod.map_snd, yonedaProdIso_hom_snd_assoc]
      rw [← Functor.map_comp_assoc, prod.lift_snd]
      exact (prod.lift_snd _ _).symm
  have hw : yoneda.map σ = 𝟙 _ ≫ yoneda.map σ := (Category.id_comp _).symm
  rw [← hs, ← ptOf_map, ← pointsMap_class, hw, ← ptOf_map, ← pointsMap_class]
  change pointsMap C S hS _ qL ((schemePointsHomeomorph C S hS (E ⨯ U)).symm (ψ t)) = _
  congr 1
  apply (schemePointsHomeomorph C S hS (E ⨯ U)).injective
  rw [Homeomorph.apply_symm_apply]
  change ψ t = pointsEquivScheme C S hS (E ⨯ U) _
  rw [pointsEquivScheme_pointsMap_yoneda C S hS, hτ, Scheme.Hom.comp_apply, hat]

/-- **A point over `L` is schematic exactly when it factors through the schematic locus.** For
an algebraic space `F` and a morphism `σ : h_{Spec L} ⟶ F`, the class of the point given by `σ`
lies in the schematic locus of `F` if and only if `σ` factors through it. -/
private theorem class_ptOf_mem_range_schematicLocus_iff {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C S hS F) (L : Type u) [Field L] [Algebra k L]
    (hL : C.Contains (Spec (.of L))) (σ : yoneda.obj (extObj C S hS e L hL) ⟶ F) :
    (ptOf C S hS e _ L hL σ).class C S hS _ ∈
        Set.range (pointsMap C S hS _ (schematicLocus C S hS F).ι) ↔
      ∃ z : yoneda.obj (extObj C S hS e L hL) ⟶ (schematicLocus C S hS F).toFunctor,
        z ≫ (schematicLocus C S hS F).ι = σ := by
  have : Subsingleton ((BigFppfOver.toScheme C S hS).obj (extObj C S hS e L hL)) :=
    inferInstanceAs (Subsingleton (Spec (.of L)))
  have : Subsingleton (points C S hS (yoneda.obj (extObj C S hS e L hL))) :=
    (pointsEquivScheme C S hS _).injective.subsingleton
  constructor
  · intro h
    refine (factorsThrough_openSubspace_iff_points C S hS hF (isAlgebraicSpace_yoneda C S hS _) _
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace C S hS hF).1 _).2 ?_
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w ((ptOf C S hS e _ L hL (𝟙 _)).class C S hS _), pointsMap_class,
      ptOf_map, Category.id_comp]
    exact h
  · rintro ⟨z, hz⟩
    refine ⟨(ptOf C S hS e _ L hL z).class C S hS _, ?_⟩
    rw [pointsMap_class, ptOf_map, hz]

/-- **The schematic locus of a base change is nonempty.** For a separated group algebraic space
`G` over `S ≅ Spec k` and an extension `L/k`, the schematic locus of `h_{Spec L} × G` is
nonempty: it contains the preimage of the schematic locus of `G`, which is dense because `G` is
decent. -/
private theorem nonempty_range_pointsMap_schematicLocus_prod
    (hsep : IsSeparatedOver C S hS G.obj.X.left) (L : Type u) [Field L] [Algebra k L]
    (hL : C.Contains (Spec (.of L))) :
    (Set.range (pointsMap C S hS _ (schematicLocus C S hS
      (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left)).ι)).Nonempty := by
  let E := extObj C S hS e L hL
  have hX : IsAlgebraicSpace C S hS G.obj.X.left := G.property
  have hY : IsAlgebraicSpace C S hS (yoneda.obj E ⨯ G.obj.X.left) :=
    isAlgebraicSpace_prod_yoneda_obj E hX
  obtain ⟨hG'o, hG'r⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace C S hS hX
  have : Nonempty (points C S hS G.obj.X.left) :=
    ⟨pointsMap C S hS _ (1 : yoneda.obj E ⟶ G.obj.X.left)
      ((ptOf C S hS e _ L hL (𝟙 _)).class C S hS _)⟩
  obtain ⟨y⟩ := (denseRange_schematicLocus_of_isDecentSpace C S hS hX
    (isDecentSpace_of_isLocallySeparatedOver C S hS hX
      (isImmersion_of_isClosedImmersion C S hS hsep))).nonempty
  have hsnd : Function.Surjective (pointsMap C S hS _
      (prod.snd : yoneda.obj E ⨯ G.obj.X.left ⟶ G.obj.X.left)) :=
    isSurjective_of_presheafSurjective C S hS _
      (presheaf_prod_snd inferInstance E G.obj.X.left (surjective_extObj C S hS e L hL))
  obtain ⟨w₀, hw₀⟩ := hsnd (pointsMap C S hS _ (schematicLocus C S hS G.obj.X.left).ι y)
  let G₁ := (schematicLocus C S hS G.obj.X.left).preimage
    (prod.snd : yoneda.obj E ⨯ G.obj.X.left ⟶ G.obj.X.left)
  have hG₁o : IsOpenSubspace C S hS G₁ := isOpenSubspace_preimage C S hS _ _ hX hY hG'o
  have hG₁r : G₁.toFunctor.IsRepresentable := by
    have hsq := Subfunctor.isPullback_preimage
      (prod.snd : yoneda.obj E ⨯ G.obj.X.left ⟶ G.obj.X.left) (schematicLocus C S hS _)
    have hsq₂ := isPullback_prod_map_id_left (schematicLocus C S hS G.obj.X.left).ι
      (yoneda.obj E)
    exact Functor.IsRepresentable.mk' ((IsPullback.isoIsPullback _ _ hsq hsq₂ ≪≫
      prod.mapIso (Iso.refl _) (schematicLocus C S hS G.obj.X.left).toFunctor.reprW.symm ≪≫
      (yonedaProdIso C S hS E _).symm).symm)
  refine ⟨w₀, range_pointsMap_ι_le_schematicLocus C S hS G₁ hG₁o hG₁r ?_⟩
  rw [range_pointsMap_preimage_ι C S hS]
  exact ⟨y, hw₀.symm⟩

/-- **A Jacobson chart whose closed points are graphs makes every point schematic.** Let `g` be
a continuous surjection from a Jacobson space onto the points of `h_{Spec L} × G` carrying closed
points to graphs of sections. Then every point of `h_{Spec L} × G` lies in its schematic locus:
the preimage of the schematic locus is open and nonempty, so it contains a closed point, and
translations move that graph onto every other one, so the preimage contains every closed point. -/
private theorem forall_mem_range_schematicLocus_of_jacobsonSpace
    (hsep : IsSeparatedOver C S hS G.obj.X.left) (L : Type u) [Field L] [Algebra k L]
    (hL : C.Contains (Spec (.of L))) {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (g : T → points C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left))
    (hgc : Continuous g) (hgs : Function.Surjective g)
    (hsec : ∀ t ∈ closedPoints T, ∃ τ : yoneda.obj (extObj C S hS e L hL) ⟶ G.obj.X.left,
      g t = (ptOf C S hS e _ L hL (prod.lift (𝟙 _) τ)).class C S hS _)
    (x : points C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left)) :
    x ∈ Set.range (pointsMap C S hS _
      (schematicLocus C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left)).ι) := by
  have hY : IsAlgebraicSpace C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left) :=
    isAlgebraicSpace_prod_yoneda_obj _ G.property
  let O : Set T := g ⁻¹' Set.range (pointsMap C S hS _
    (schematicLocus C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left)).ι)
  have hOo : IsOpen O := (isOpen_range_pointsMap_of_isOpenImmersion C S hS _
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace C S hS hY).1.2).preimage
      hgc
  obtain ⟨x₀, hx₀⟩ := nonempty_range_pointsMap_schematicLocus_prod e G hsep L hL
  obtain ⟨t₀, rfl⟩ := hgs x₀
  obtain ⟨c₀, hc₀O, hc₀cl⟩ := nonempty_inter_closedPoints (⟨t₀, hx₀⟩ : O.Nonempty)
    hOo.isLocallyClosed
  obtain ⟨τ₀, hτ₀⟩ := hsec c₀ hc₀cl
  have hfac₀ := (class_ptOf_mem_range_schematicLocus_iff e hY L hL _).1 (by rwa [← hτ₀])
  have hcl : closedPoints T ⊆ O := by
    intro c hc
    obtain ⟨τ, hτ⟩ := hsec c hc
    rw [Set.mem_preimage, hτ]
    exact (class_ptOf_mem_range_schematicLocus_iff e hY L hL _).2
      (graph_factors_schematicLocus G τ τ₀ hfac₀)
  obtain ⟨t, rfl⟩ := hgs x
  by_contra hne
  obtain ⟨c, hcO, hccl⟩ := nonempty_inter_closedPoints (⟨t, hne⟩ : Oᶜ.Nonempty)
    hOo.isClosed_compl.isLocallyClosed
  exact hcO (hcl hccl)

/-- **Over a large algebraically closed field the base change of a separated group algebraic
space is schematic at every point.** Let `G` be a separated group algebraic space over
`S ≅ Spec k`. There is a cardinal `κ`, below the cutoff of the site, such that for every
algebraically closed extension `L/k` with `κ < #L` whose spectrum lies in the site, every point
of `h_{Spec L} × G` lies in its schematic locus.

This is the heart of Stacks 0B8E. Choose an atlas `U ⟶ G`. For `L` large, `U_L` is a Jacobson
scheme whose closed points are `L`-rational (Stacks 0479). The schematic locus of `G_L` is open
and nonempty, since it contains `L × G'` for the schematic locus `G'` of `G`, which is dense
(Stacks 06NH) because `G` is decent. So its preimage in `U_L` is a nonempty open, which contains a
closed point, an `L`-rational point. Translations of `G_L` by sections over `L` preserve the
schematic locus and act transitively on sections, so every `L`-rational point of `G_L`, and in
particular the image of every closed point of `U_L`, lies in the schematic locus. A nonempty
closed subset of a Jacobson space contains a closed point, so the preimage is all of `U_L`, and
`U_L ⟶ G_L` is surjective. -/
theorem exists_cardinal_mem_schematicLocus_prod (hsep : IsSeparatedOver C S hS G.obj.X.left) :
    ∃ κ : Cardinal.{u}, κ < C.cutoff ∧ ∀ (L : Type u) [Field L] [Algebra k L] [IsAlgClosed L]
      (hL : C.Contains (Spec (.of L))), κ < Cardinal.mk L →
      ∀ x : points C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left),
        x ∈ Set.range (pointsMap C S hS _
          (schematicLocus C S hS (yoneda.obj (extObj C S hS e L hL) ⨯ G.obj.X.left)).ι) := by
  classical
  have hX : IsAlgebraicSpace C S hS G.obj.X.left := G.property
  obtain ⟨U, q, hqs, -⟩ := hX.exists_atlas
  let f : (BigFppfOver.toScheme C S hS).obj U ⟶ Spec (.of k) :=
    (BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U) ≫ e.hom
  refine ⟨((BigFppfOver.toScheme C S hS).obj U).size, U.left.property, fun L _ _ _ hL hκ x => ?_⟩
  let E := extObj C S hS e L hL
  -- the scheme `T' = U ×_k Spec L`
  let φL : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have := jacobsonSpace_pullback_of_size_lt k _ f L hκ
  have hres :=
    Stacks.AlgebraicGeometry.ClosedPointResidue.isAlgebraicResidue_of_mem_closedPoints_of_size_lt
      k _ f L hκ
  obtain ⟨ψ, hψsurj, hlift⟩ := exists_surjective_pullback_toScheme_prod_extObj e U L hL
  -- the chart `h_{E ⨯ U} ⟶ h_E ⨯ G` and the induced continuous surjection `T' ⟶ |G_L|`
  let qL : yoneda.obj (E ⨯ U) ⟶ yoneda.obj E ⨯ G.obj.X.left :=
    (yonedaProdIso C S hS E U).hom ≫ prod.map (𝟙 _) q
  have hqLsurj : Function.Surjective (pointsMap C S hS _ qL) := by
    rw [pointsMap_comp]
    exact (surjective_pointsMap_of_isPullback C S hS (isPullback_prod_map_id_left q (yoneda.obj E))
      (surjective_pointsMap_of_presheaf_surjective C S hS q hqs)).comp
      (pointsHomeomorphOfIso C S hS (yonedaProdIso C S hS E U)).surjective
  let H₀ := schemePointsHomeomorph C S hS (E ⨯ U)
  let T' : Scheme.{u} := pullback f φL
  let g : T' → points C S hS (yoneda.obj E ⨯ G.obj.X.left) :=
    fun t => pointsMap C S hS _ qL (H₀.symm (ψ t))
  have hgc : Continuous g :=
    (continuous_pointsMap C S hS qL).comp (H₀.symm.continuous.comp ψ.continuous)
  have hgs : Function.Surjective g := hqLsurj.comp (H₀.symm.surjective.comp hψsurj)
  -- closed points of `T'` give sections of `G_L ⟶ Spec L`
  have hsec : ∀ t ∈ closedPoints T', ∃ τ : yoneda.obj E ⟶ G.obj.X.left,
      g t = (ptOf C S hS e _ L hL (prod.lift (𝟙 _) τ)).class C S hS _ := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := exists_section_of_isAlgebraic_residueField L T'
      (pullback.snd f φL) t (hres t ht)
    obtain ⟨τ, hτ⟩ := hlift a ha
    exact ⟨yoneda.map τ ≫ q, pointsMap_symm_eq_class_ptOf_prod_lift e q L hL ψ a t hat τ hτ⟩
  exact forall_mem_range_schematicLocus_of_jacobsonSpace e G hsep L hL g hgc hgs hsec x

end LargeField

/-! ### Some algebraically closed base change is a scheme -/

section SomeField

variable {k : Type u} [Field k]

/-- **Over some algebraically closed field the base change of a separated group algebraic space
is a scheme.** Let `G` be a separated group algebraic space over `Spec k`. There is an
algebraically closed extension `L/k`, with `Spec L` in the site, such that the restriction
`G_L` of `G` to the big fppf site of `Spec L` is representable.

Take `L` of cardinality above the bound of
`AlgebraicGeometry.Space.GroupOverField.exists_cardinal_mem_schematicLocus_prod`; the site
contains such fields because its cutoff is a strong limit. Then the schematic locus of
`h_{Spec L} × G` is everything, so that product is representable, and Stacks 02W6 turns this
into representability of the restriction to the site of `Spec L`. -/
theorem exists_isAlgClosed_isRepresentable_relocalizeRestrict (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace B (Spec (.of k)) hk (yoneda.obj (⊤_ (BigFppfOver B (Spec (.of k)) hk)))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _))
    (hsep : IsSeparatedOver B (Spec (.of k)) hk G.obj.X.left) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsAlgClosed L)
      (hL : B.Contains (Spec (.of L))),
      ((OverShriek.relocalizeRestrict (specExtensionHom k L B hk hL)).obj
        G.obj.X.left).IsRepresentable := by
  obtain ⟨κ, hκc, hκ⟩ := exists_cardinal_mem_schematicLocus_prod (Iso.refl _) G hsep
  obtain ⟨L, _, _, _, hL, hκL⟩ := exists_large_algClosed_contained B k hk κ hκc
  refine ⟨L, inferInstance, inferInstance, inferInstance, hL, ?_⟩
  let E := extObj B (Spec (.of k)) hk (Iso.refl _) L hL
  have hY : IsAlgebraicSpace B (Spec (.of k)) hk (yoneda.obj E ⨯ G.obj.X.left) :=
    isAlgebraicSpace_prod_yoneda_obj E G.property
  obtain ⟨hZo, hZr⟩ := isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
    B (Spec (.of k)) hk hY
  have : IsIso (schematicLocus B (Spec (.of k)) hk (yoneda.obj E ⨯ G.obj.X.left)).ι :=
    isIso_of_isOpenImmersion_of_surjective_pointsMap B (Spec (.of k)) hk _ hZo.2
      (hκ L hL hκL)
  have hprod : (yoneda.obj E ⨯ G.obj.X.left).IsRepresentable :=
    isRepresentable_of_natIso _
      (asIso (schematicLocus B (Spec (.of k)) hk (yoneda.obj E ⨯ G.obj.X.left)).ι)
  let eE : E ≅ Over.mk (specExtensionHom k L B hk hL) :=
    Over.isoMk (Iso.refl _) (by
      apply ObjectProperty.hom_ext
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])
  exact (isRepresentable_overMap_iff (Over.mk (specExtensionHom k L B hk hL)) G.obj.X.left).2
    (isRepresentable_of_natIso _ (prod.mapIso (yoneda.mapIso eE) (Iso.refl _)))

end SomeField

/-! ### Stacks 0B8E -/

section AlgebraicClosure

variable {k : Type u} [Field k]

/-- Let `k` be a field with algebraic closure `k̄` and let `G` be a separated group algebraic
space over `k`. Then `G_{k̄}` is a scheme.

By `AlgebraicGeometry.Space.GroupOverField.exists_isAlgClosed_isRepresentable_relocalizeRestrict`
the base change `G_L` is a scheme for some algebraically closed extension `L/k`; this is the
source's argument with translations of the group and Jacobson charts. A separated algebraic space
over the affine `Spec k` is quasi-separated, so Stacks 0B84 part (1) descends this to `k̄`. -/
@[stacks 0B8E]
theorem isRepresentable_relocalizeRestrict_algebraicClosure_of_isSeparatedOver
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (G : GroupAlgebraicSpace B (Spec (.of k)) hk (yoneda.obj (⊤_ (BigFppfOver B (Spec (.of k)) hk)))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _))
    (hsep : IsSeparatedOver B (Spec (.of k)) hk G.obj.X.left) :
    ((OverShriek.relocalizeRestrict (specExtensionHom k (AlgebraicClosure k) B hk
      (contains_spec_of_isAlgebraic B k (AlgebraicClosure k) hk))).obj
        G.obj.X.left).IsRepresentable := by
  obtain ⟨L, _, _, _, hL, hrep⟩ := exists_isAlgClosed_isRepresentable_relocalizeRestrict B hk G hsep
  exact isRepresentable_relocalizeRestrict_algebraicClosure k L B hk hL G.obj.X.left G.property
    (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B _ hk B.contains_terminal _
      ((isAbsolutelySeparated_iff_isSeparatedOver B _ hk B.contains_terminal
        (inferInstance : IsAffine (Spec (.of k))) G.property).2 hsep)) hrep

end AlgebraicClosure

end AlgebraicGeometry.Space.GroupOverField

end
