module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Surjectivity of the conormal sheaf map of a cartesian square of immersions

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a cartesian square of schemes with `i` and `i'` immersions. The canonical map
`f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 01R4] is then surjective.

## Main results

* `Stacks.Immersion.epi_immersionConormalSheafMap`: the canonical map is an epimorphism.

## References

* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace Stacks.Immersion

variable {Z X Z' X' : Scheme.{u}}

/-! ### Affine charts of a square of immersions -/

/-- An affine chart of a square of immersions: a pair of affine opens `U ⊆ X` and `V ⊆ X'` with
`g(U) ⊆ V` over which both `i` and `i'` restrict to closed immersions. -/
private structure SquareChart (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X') where
  /-- The affine open of the ambient scheme upstairs. -/
  source : X.affineOpens
  /-- The affine open of the ambient scheme downstairs. -/
  target : X'.affineOpens
  /-- The chart is compatible with the ambient morphism. -/
  le_preimage : source.1 ≤ g ⁻¹ᵁ target.1
  /-- The immersion upstairs restricts to a closed immersion over the chart. -/
  source_closed : IsClosedImmersion (i.resLE source.1 (i ⁻¹ᵁ source.1) le_rfl)
  /-- The immersion downstairs restricts to a closed immersion over the chart. -/
  target_closed : IsClosedImmersion (i'.resLE target.1 (i' ⁻¹ᵁ target.1) le_rfl)

/-- The affine model ideal of a chart is the kernel of the map on sections. -/
private theorem affineModel_ideal_eq_chartIdeal (i : Z ⟶ X) (U : X.Opens) (hU : IsAffineOpen U)
    (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing I))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I) :
    RingHom.ker (i.app U).hom = I := by
  rw [Scheme.Hom.app_eq_appLE]
  exact Stacks.Conormal.ker_appLE_eq_of_affineModel i U hU I e he

/-- The opens `i ⁻¹ᵁ U`, for `U` the ambient open of an affine chart of the square, form a basis
of the topology of `Z`. -/
private theorem squareChart_isBasis (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : i ≫ g = f ≫ i') :
    Opens.IsBasis (Set.range fun C : SquareChart i i' g => i ⁻¹ᵁ C.source.1) := by
  rw [Opens.isBasis_iff_nbhd]
  intro O z hz
  have hb := X.isBasis_affineOpens.of_isInducing i.isEmbedding.isInducing
  obtain ⟨V, ⟨U₀, hU₀, rfl⟩, hzU₀, hU₀O⟩ := Opens.isBasis_iff_nbhd.mp hb hz
  have hcomm : g (i z) = i' (f z) := congrArg (fun h : Z ⟶ X' => h z) comm
  have hz' : g (i z) ∈ i'.coborderRange := by
    rw [hcomm]
    exact subset_coborder ⟨f z, rfl⟩
  obtain ⟨V', hV'a, hzV', hV'⟩ := Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hz'
  have hzU : i z ∈ U₀ ⊓ i.coborderRange ⊓ g ⁻¹ᵁ V' :=
    ⟨⟨hzU₀, subset_coborder ⟨z, rfl⟩⟩, hzV'⟩
  obtain ⟨U, hUa, hzU, hU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hzU
  let C : SquareChart i i' g :=
    ⟨⟨U, hUa⟩, ⟨V', hV'a⟩, hU.trans inf_le_right,
      isClosedImmersion_resLE_of_le_coborderRange i U
        (hU.trans (inf_le_left.trans inf_le_right)),
      isClosedImmersion_resLE_of_le_coborderRange i' V' hV'⟩
  exact ⟨i ⁻¹ᵁ U, ⟨C, rfl⟩, hzU,
    (i.preimage_mono (hU.trans (inf_le_left.trans inf_le_left))).trans hU₀O⟩

/-! ### The chart ideal of a cartesian square -/

/-- For a cartesian square of schemes and affine opens `U ⊆ X`, `V ⊆ X'` with `g(U) ⊆ V` over
which `i'` restricts to a closed immersion, the square of rings of sections over `U`, `V` and their
preimages is a pushout. -/
private theorem isPushout_appLE_of_chart (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (sq : IsPullback i f g i') (U : X.affineOpens) (V : X'.affineOpens)
    (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (hcl : IsClosedImmersion (i'.resLE V.1 (i' ⁻¹ᵁ V.1) le_rfl)) :
    IsPushout (g.appLE V.1 U.1 hUV) (i'.app V.1) (i.app U.1)
      (f.appLE (i' ⁻¹ᵁ V.1) (i ⁻¹ᵁ U.1) (preimage_le_preimage_of_square sq.w U.1 V.1 hUV)) := by
  let _ : IsClosedImmersion (i'.resLE V.1 (i' ⁻¹ᵁ V.1) le_rfl) := hcl
  have hle := preimage_le_preimage_of_square sq.w U.1 V.1 hUV
  have hsq := Scheme.Hom.isPullback_resLE sq (US := V.1) (UT := i' ⁻¹ᵁ V.1)
    (UX := U.1) le_rfl hUV (UY := i ⁻¹ᵁ U.1) (by exact (inf_eq_left.mpr hle).symm)
  have : IsAffine (i' ⁻¹ᵁ V.1).toScheme :=
    isAffine_of_isAffineHom (i'.resLE V.1 (i' ⁻¹ᵁ V.1) le_rfl)
  have hr := isPushout_appTop_of_isPullback hsq
  refine hr.of_iso V.1.topIso U.1.topIso (i' ⁻¹ᵁ V.1).topIso (i ⁻¹ᵁ U.1).topIso ?_ ?_ ?_ ?_
  · exact (arrowResLEAppIso g V.1 U.1 hUV).hom.w.symm
  · rw [← Scheme.Hom.appLE_eq_app]
    exact (arrowResLEAppIso i' V.1 (i' ⁻¹ᵁ V.1) le_rfl).hom.w.symm
  · rw [← Scheme.Hom.appLE_eq_app]
    exact (arrowResLEAppIso i U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.w.symm
  · exact (arrowResLEAppIso f (i' ⁻¹ᵁ V.1) (i ⁻¹ᵁ U.1) hle).hom.w.symm

/-- Over an affine chart of a cartesian square of immersions, the kernel ideal upstairs is the
extension of the kernel ideal downstairs. -/
private theorem chart_ker_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (sq : IsPullback i f g i') (C : SquareChart i i' g) :
    RingHom.ker (i.app C.source.1).hom =
      (RingHom.ker (i'.app C.target.1).hom).map
        (g.appLE C.target.1 C.source.1 C.le_preimage).hom :=
  ker_eq_map_ker_of_pushout
    (isPushout_appLE_of_chart i i' f g sq C.source C.target C.le_preimage C.target_closed)
    (app_surjective_of_closedRestriction i' C.target C.target_closed)

/-! ### Surjectivity from generation on a basis -/

/-- A morphism `φ` out of a pullback sheaf of modules is an epimorphism if the opens `B j` form a
basis of the source, each lies over `W j`, and the sections of the target over `B j` are spanned by
the restrictions of the transposed sections of `φ` over `W j`. -/
private theorem epi_of_span_on_basis {Y Y' : Scheme.{u}} (f : Y ⟶ Y')
    {F : SheafOfModules.{u} (structureSheafRing Y'.toLocallyRingedSpace.toRingedSpace)}
    {G : SheafOfModules.{u} (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace)}
    (φ : (modulePullback f.toLRSHom.toShHom).obj F ⟶ G)
    {ι : Type*} (B : ι → Y.Opens) (hB : Opens.IsBasis (Set.range B))
    (W : ι → Y'.Opens) (hBW : ∀ j, B j ≤ f ⁻¹ᵁ W j)
    (hspan : ∀ j, Submodule.span
      ((structureSheafRing Y.toLocallyRingedSpace.toRingedSpace).obj.obj (op (B j)))
      (M := G.val.obj (op (B j)))
      (Set.range fun a : F.val.obj (op (W j)) =>
        G.val.map (homOfLE (hBW j)).op
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ φ).val.app
            (op (W j)) a)) = ⊤) :
    Epi φ := by
  constructor
  intro N p q hpq
  have h := congrArg ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv F N) hpq
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right] at h
  refine SheafOfModules.hom_ext ((PresheafOfModules.toPresheaf _).map_injective ?_)
  refine TopCat.Sheaf.hom_ext (B := B) _
    (show TopCat.Sheaf _ Y.carrier from ⟨N.val.presheaf, N.isSheaf⟩) hB (fun j => ?_)
  suffices hall : ∀ y : G.val.obj (op (B j)),
      p.val.app (op (B j)) y = q.val.app (op (B j)) y by
    ext y
    exact hall y
  intro y
  have hy : y ∈ Submodule.span
      ((structureSheafRing Y.toLocallyRingedSpace.toRingedSpace).obj.obj (op (B j)))
      (M := G.val.obj (op (B j)))
      (Set.range fun a : F.val.obj (op (W j)) =>
        G.val.map (homOfLE (hBW j)).op
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ φ).val.app
            (op (W j)) a)) :=
    hspan j ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h2 := congr($(h).val.app (op (W j)) a)
    simp only [comp_val_app_apply, modulePushforward_map_val_app_preimage] at h2
    exact (val_app_naturality p (homOfLE (hBW j)) _).trans
      ((val_map_congr _ h2).trans (val_app_naturality q (homOfLE (hBW j)) _).symm)
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul r x hx ih => simp only [map_smul, ih]

/-! ### The scalar action on pushforward sections -/

/-- The sections of a pushforward sheaf of modules over an open `A` of the target are those of
the sheaf over `p⁻¹A`, and a function on `A` acts on them through `p^♯`. -/
private theorem pushforward_smul_section {Y Y' : Scheme.{u}} (p : Y ⟶ Y')
    (M : SheafOfModules.{u} (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace))
    (A : Y'.Opens)
    (r : (structureSheafRing Y'.toLocallyRingedSpace.toRingedSpace).obj.obj (op A))
    (x : ((modulePushforward p.toLRSHom.toShHom).obj M).val.obj (op A)) :
    r • x =
      (show ((modulePushforward p.toLRSHom.toShHom).obj M).val.obj (op A) from
        (show (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace).obj.obj (op (p ⁻¹ᵁ A)) from
            (p.app A).hom (show Γ(Y', A) from r)) •
          (show M.val.obj (op (p ⁻¹ᵁ A)) from x)) := rfl

/-! ### The conormal module of an extended ideal is generated by the extended classes -/

/-- For a ring map `φ : R →+* S` and an ideal `J ⊆ R` with extension `I = J · S`, the classes in
`I/I²` of the elements `φ a` for `a : J` span `I/I²` over `S`. -/
private theorem cotangent_span_map {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (J : Ideal R) (I : Ideal S) (hI : I = J.map φ) (hmem : ∀ a : J, φ (a : R) ∈ I) :
    Submodule.span S (Set.range fun a : J => I.toCotangent ⟨φ (a : R), hmem a⟩) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  have hle : Submodule.span S (φ '' (J : Set R)) ≤ I := by rw [hI, Ideal.map]
  have aux : ∀ b : S, b ∈ Submodule.span S (φ '' (J : Set R)) → ∀ hb : b ∈ I,
      I.toCotangent ⟨b, hb⟩ ∈
        Submodule.span S (Set.range fun a : J => I.toCotangent ⟨φ (a : R), hmem a⟩) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, ha, rfl⟩ := hb
      intro hbI
      exact Submodule.subset_span ⟨⟨a, ha⟩, congrArg I.toCotangent (Subtype.ext rfl)⟩
    | zero =>
      intro hbI
      rw [show (⟨(0 : S), hbI⟩ : I) = 0 from Subtype.ext rfl, map_zero]
      exact Submodule.zero_mem _
    | add b c hb hc ihb ihc =>
      intro hbI
      rw [show (⟨b + c, hbI⟩ : I) = ⟨b, hle hb⟩ + ⟨c, hle hc⟩ from Subtype.ext rfl, map_add]
      exact Submodule.add_mem _ (ihb (hle hb)) (ihc (hle hc))
    | smul s b hb ih =>
      intro hbI
      rw [show (⟨s • b, hbI⟩ : I) = s • (⟨b, hle hb⟩ : I) from Subtype.ext rfl, map_smul]
      exact Submodule.smul_mem _ s (ih (hle hb))
  exact aux x (hI ▸ x.2) x.2

/-! ### Generation over an affine chart -/

/-- Over an affine chart of a cartesian square of immersions, any submodule of the conormal
sections over `i⁻¹U` containing the restrictions of all transposed sections of the canonical map
over `i'⁻¹V` is everything. -/
private theorem chart_conormal_span (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (sq : IsPullback i f g i') (C : SquareChart i i' g)
    (P : Submodule
      ((structureSheafRing Z.toLocallyRingedSpace.toRingedSpace).obj.obj (op (i ⁻¹ᵁ C.source.1)))
      ((conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (op (i ⁻¹ᵁ C.source.1))))
    (hP : ∀ a : (conormalSheaf i'.liftCoborder.toLRSHom.toShHom).val.obj
        (op (i' ⁻¹ᵁ C.target.1)),
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
          (homOfLE (preimage_le_preimage_of_square sq.w C.source.1 C.target.1
            C.le_preimage)).op
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
              (immersionConormalSheafMap i i' f g (toShHom_square sq.w))).val.app
            (op (i' ⁻¹ᵁ C.target.1)) a) ∈ P) :
    P = ⊤ := by
  classical
  obtain ⟨I, eZ, heZ⟩ :=
    Conormal.exists_affineModel_of_resLE i C.source.1 C.source.2 C.source_closed
  obtain ⟨J, eW, heW⟩ :=
    Conormal.exists_affineModel_of_resLE i' C.target.1 C.target.2 C.target_closed
  have hker : I = J.map (g.appLE C.target.1 C.source.1 C.le_preimage).hom := by
    rw [← affineModel_ideal_eq_chartIdeal i C.source.1 C.source.2 I eZ heZ,
      ← affineModel_ideal_eq_chartIdeal i' C.target.1 C.target.2 J eW heW]
    exact chart_ker_eq i i' f g sq C
  have hmem : ∀ a : J,
      (g.appLE C.target.1 C.source.1 C.le_preimage).hom (a : Γ(X', C.target.1)) ∈ I := by
    intro a
    rw [hker]
    exact Ideal.mem_map_of_mem _ a.2
  let _inst : Module
      ((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op C.source.1))
      I.Cotangent := inferInstanceAs (Module Γ(X, C.source.1) I.Cotangent)
  have hform := isInducedConormalSheafMap_immersionConormalSheafMap i i' f g sq.w
    C.source.1 C.source.2 C.target.1 C.target.2 C.le_preimage I J eZ heZ eW heW
  let Q : Submodule
      ((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op C.source.1))
      (((modulePushforward i.toLRSHom.toShHom).obj
        (conormalSheaf i.liftCoborder.toLRSHom.toShHom)).val.obj (op C.source.1)) :=
    { carrier := fun w => w ∈ P
      add_mem' := fun hx hy => P.add_mem hx hy
      zero_mem' := P.zero_mem
      smul_mem' := fun c w hw => by
        rw [pushforward_smul_section i (conormalSheaf i.liftCoborder.toLRSHom.toShHom)
          C.source.1 c w]
        exact P.smul_mem _ hw }
  set e := Stacks.Conormal.affineConormalIsoCotangent i C.source.1 C.source.2 I eZ heZ
  have hgen : ∀ a : J, I.toCotangent ⟨_, hmem a⟩ ∈ Submodule.comap e.inv.hom Q := fun a =>
    Submodule.mem_comap.mpr
      ((congrArg (fun w => w ∈ Q) (hform a ⟨_, hmem a⟩ rfl)).mp (hP _))
  have hle : Submodule.span ((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj
        (op C.source.1))
      (Set.range fun a : J => I.toCotangent ⟨_, hmem a⟩) ≤ Submodule.comap e.inv.hom Q :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  have hspan : e.hom.hom y ∈
      Submodule.span
        ((structureSheafRing X.toLocallyRingedSpace.toRingedSpace).obj.obj (op C.source.1))
        (Set.range fun a : J => I.toCotangent ⟨_, hmem a⟩) :=
    Submodule.eq_top_iff'.mp
      (cotangent_span_map (g.appLE C.target.1 C.source.1 C.le_preimage).hom J I hker hmem)
      (e.hom.hom y)
  have hy := Submodule.mem_comap.mp (hle hspan)
  have hback := (ModuleCat.hom_comp_apply e.hom e.inv y).symm.trans
    (ModuleCat.hom_apply_congr e.hom_inv_id y)
  exact (congrArg (fun w => w ∈ Q) hback).mp hy

/-! ### Surjectivity -/

/-- For a cartesian square of schemes whose horizontal maps `i` and `i'` are immersions, the
canonical map `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of conormal sheaves is an epimorphism. -/
@[stacks 0473 "surjectivity"]
theorem epi_immersionConormalSheafMap (i : Z ⟶ X) (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i']
    (f : Z ⟶ Z') (g : X ⟶ X') (sq : IsPullback i f g i') :
    Epi (immersionConormalSheafMap i i' f g (toShHom_square sq.w)) :=
  epi_of_span_on_basis f _ (fun C : SquareChart i i' g => i ⁻¹ᵁ C.source.1)
    (squareChart_isBasis i i' f g sq.w) (fun C => i' ⁻¹ᵁ C.target.1)
    (fun C => preimage_le_preimage_of_square sq.w C.source.1 C.target.1 C.le_preimage)
    (fun C => chart_conormal_span i i' f g sq C _ (fun a => Submodule.subset_span ⟨a, rfl⟩))

end Stacks.Immersion

end
