module

public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInjective
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentation
public import StacksFrontier.Deformation.RingedSpaceThickening.FirstOrderIdealMapIso
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAutomorphisms

/-!
# Solutions of a ringed space deformation problem as square-zero extensions on `X`

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})`, `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, `𝒢` and `c` be the data of the
deformation problem of **Stacks 08U7**.  A solution
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution` is a first order thickening
`i : X ⟶ X'` of ringed spaces with a morphism `f' : X' ⟶ S'` and an identification of its ideal
with `𝒢`.  The underlying map of `i` is a homeomorphism, so `𝒪_{X'}` may be read on the opens of
`X`, where it is an extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `(f ∘ t)⁻¹𝒪_{S'}`-algebras: an
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension (f ≫ t) G`, the object whose
classes the library measures in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)`.

This file builds that passage.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.adjointBase`: the adjoint
  `𝒪_T ⟶ g_* 𝒪_{X'}` of the algebra structure `g⁻¹𝒪_T ⟶ 𝒪_{X'}` of an extension.
* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.IdealBijective`: the
  identification of the square-zero ideal with `𝒢` is bijective on sections.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedSheaf`: `𝒪_{X'}` read
  as a sheaf of rings on the opens of `X`.
* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.toAlgebraExtension`: a solution
  read as a square-zero extension of `(f ∘ t)⁻¹𝒪_{S'}`-algebras on `X`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.toAlgebraExtension_idealBijective`:
  the ideal of the extension attached to a solution is identified with `𝒢` bijectively.

## Implementation notes

`𝒪_{X'}` is transported to `X` by pushing it forward along the inverse of the homeomorphism
underlying `i`, which is
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedPresheaf`: its sections
over an open of `X` are, definitionally, the sections of `𝒪_{X'}` over the matching open of
`X'`.  The reduction is
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.thickenedReduction`, and the
identification of the ideal with `𝒢` is read on sections through
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.incl` and
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.descendSection`.

## References

* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08UY](https://stacks.math.columbia.edu/tag/08UY)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Two notions attached to a square-zero extension -/

namespace AlgebraSquareZeroExtension

variable {X T : RingedSpace.{u, u}} {g : X ⟶ T}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- The adjoint `𝒪_T ⟶ g_* 𝒪_{X'}` of the algebra structure `g⁻¹𝒪_T ⟶ 𝒪_{X'}` of a square-zero
extension, under `g⁻¹ ⊣ g_*`. -/
abbrev adjointBase (P : AlgebraSquareZeroExtension g G) :
    T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj P.sheaf :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _ P.base

/-- The identification of the square-zero ideal `Ker(𝒪_{X'} ⟶ 𝒪_X)` with `𝒢` is bijective on
the sections over every open. -/
abbrev IdealBijective (P : AlgebraSquareZeroExtension g G) : Prop :=
  ∀ U : (Opens X.carrier)ᵒᵖ, Function.Bijective (P.ideal.app U)

end AlgebraSquareZeroExtension

/-- Restriction along an equality of opens is bijective on the sections of a sheaf of
modules. -/
theorem map_eqToHom_bijective {Y : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Y))
    {U V : (Opens Y.carrier)ᵒᵖ} (e : U = V) : Function.Bijective (M.val.map (eqToHom e)) := by
  subst e
  have h : ∀ m : M.val.obj U, M.val.map (eqToHom (rfl : U = U)) m = m := fun m => by
    simp only [eqToHom_refl, PresheafOfModules.map_id]
    rfl
  exact ⟨fun a b hab => (h a).symm.trans (hab.trans (h b)), fun m => ⟨m, h m⟩⟩

/-! ### A solution read on the opens of `X` -/

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-- `𝒪_{X'}` read as a sheaf of commutative rings on the opens of `X`: its pushforward along the
inverse of the homeomorphism underlying the thickening.  Its underlying presheaf is
`thickenedPresheaf`. -/
abbrev thickenedSheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} Q.baseIso.inv).obj Q.X'.sheaf

/-- The reduction `𝒪_{X'} ⟶ 𝒪_X` of a solution, as a morphism of sheaves of rings on the opens
of `X`. -/
abbrev thickenedSheafReduction : Q.thickenedSheaf ⟶ X.sheaf :=
  ObjectProperty.homMk Q.thickenedReduction

/-- The inverse homeomorphism followed by the composite `X ⟶ S'` is the map underlying
`f' : X' ⟶ S'`. -/
theorem baseIso_inv_comp_base : Q.baseIso.inv ≫ (f ≫ t).hom.base = Q.f'.hom.base := by
  have h : Q.i.hom.base ≫ Q.f'.hom.base = (f ≫ t).hom.base :=
    congrArg (fun m : X ⟶ S' => m.hom.base) Q.comm
  rw [← h, ← Category.assoc, ← baseIso_hom, Iso.inv_hom_id, Category.id_comp]

/-- The open of `X'` lying over an open `V` of `S'` is the open matching the preimage of `V` in
`X`. -/
theorem opens_map_f' (V : Opens S'.carrier) :
    (Opens.map Q.f'.hom.base).obj V =
      (Opens.map Q.baseIso.inv).obj ((Opens.map (f ≫ t).hom.base).obj V) := by
  rw [← Opens.map_comp_obj, baseIso_inv_comp_base]

/-- The comorphism `𝒪_{S'} ⟶ (f ∘ t)_* 𝒪_{X'}` of the morphism `f' : X' ⟶ S'`, read on the opens
of `X`. -/
def deformedBasePresheafMap :
    S'.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).obj
      Q.thickenedPresheaf where
  app V := Q.f'.hom.c.app V ≫ Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_map_f' V.unop)))
  naturality {V W} k := by
    have hnat := Q.f'.hom.c.naturality k
    simp only [TopCat.Presheaf.pushforward_obj_map] at hnat ⊢
    rw [reassoc_of% hnat]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun m => Q.f'.hom.c.app V ≫ Q.X'.presheaf.map m) (Subsingleton.elim _ _)

/-- `deformedBasePresheafMap`, on sections. -/
theorem deformedBasePresheafMap_app (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) :
    (Q.deformedBasePresheafMap.app V).hom s =
      (Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_map_f' V.unop)))).hom
        ((Q.f'.hom.c.app V).hom s) :=
  rfl

/-- The comorphism of `f'`, read on the opens of `X`, as a morphism of sheaves. -/
abbrev deformedBaseSheafMap :
    S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).obj
      Q.thickenedSheaf :=
  ObjectProperty.homMk Q.deformedBasePresheafMap

/-- The `(f ∘ t)⁻¹𝒪_{S'}`-algebra structure of `𝒪_{X'}` read on the opens of `X`: the adjoint
of the comorphism of `f'`. -/
def thickenedSheafBase : inverseImageBaseRing (f ≫ t) ⟶ Q.thickenedSheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv
    S'.sheaf Q.thickenedSheaf).symm Q.deformedBaseSheafMap

/-- The comorphism of `f'` followed by the reduction is the comorphism of the composite
`X ⟶ S'`, on the opens of `X`. -/
theorem deformedBasePresheafMap_comp_reduction :
    Q.deformedBasePresheafMap ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map
          Q.thickenedReduction =
      (f ≫ t).hom.c := by
  refine NatTrans.ext (funext fun V => ?_)
  have hcomm : (f ≫ t).hom = (Q.i ≫ Q.f').hom := congrArg (fun m : X ⟶ S' => m.hom) Q.comm.symm
  have hnat := Q.i.hom.c.naturality (eqToHom (congrArg op (Q.opens_map_f' V.unop)))
  have hL : (Q.deformedBasePresheafMap ≫
        (TopCat.Presheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map
          Q.thickenedReduction).app V =
      Q.f'.hom.c.app V ≫ Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_map_f' V.unop))) ≫
        Q.i.hom.c.app (op ((Opens.map Q.baseIso.inv).obj ((Opens.map (f ≫ t).hom.base).obj
          V.unop))) ≫
        X.presheaf.map (Q.roundTripHom (op ((Opens.map (f ≫ t).hom.base).obj V.unop))) := by
    rw [NatTrans.comp_app, TopCat.Presheaf.pushforward_map_app', thickenedReduction,
      NatTrans.comp_app, Functor.whiskerLeft_app, pushforwardRoundTrip_hom_app]
    rfl
  rw [hL, PresheafedSpace.congr_app hcomm V, reassoc_of% hnat]
  exact congrArg (fun m => Q.f'.hom.c.app V ≫ Q.i.hom.c.app _ ≫ m)
    ((X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _)))

/-- The `(f ∘ t)⁻¹𝒪_{S'}`-algebra structure of `𝒪_{X'}` is compatible with the reduction: the
reduction is a morphism of `(f ∘ t)⁻¹𝒪_{S'}`-algebras. -/
theorem thickenedSheafBase_comp_reduction :
    Q.thickenedSheafBase ≫ Q.thickenedSheafReduction = structureRingMap (f ≫ t) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv_naturality_right_symm Q.deformedBaseSheafMap
      Q.thickenedSheafReduction).symm.trans
    (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv S'.sheaf X.sheaf).symm
      (ObjectProperty.hom_ext _ Q.deformedBasePresheafMap_comp_reduction))

/-- The adjoint of the algebra structure is the comorphism of `f'`. -/
theorem adjoint_thickenedSheafBase :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv _ _
        Q.thickenedSheafBase = Q.deformedBaseSheafMap :=
  Equiv.apply_symm_apply _ _

/-- A section of `𝒪_{X'}` over the open matching `U` which the reduction kills lies in the ideal
of the thickening. -/
theorem reduction_eq_zero_of_mem_kernelIdeal {U : (Opens X.carrier)ᵒᵖ}
    (x : kernelIdeal Q.thickenedSheafReduction.hom U) :
    Q.reduction (U := (Opens.map Q.baseIso.inv).op.obj U) x.1 = 0 :=
  Q.comorphism_eq_zero_of_thickenedReduction_eq_zero x.1 x.2

/-- The section of `i_* 𝒢` over the open of `X'` matching `U` which a kernel section of the
reduction is the image of. -/
def kernelSection {U : (Opens X.carrier)ᵒᵖ} (x : kernelIdeal Q.thickenedSheafReduction.hom U) :
    ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U) :=
  Classical.choose (Q.exists_incl x.1 (Q.reduction_eq_zero_of_mem_kernelIdeal x))

/-- The image of the kernel section of `x` under the inclusion of `i_* 𝒢` is `x`. -/
theorem incl_kernelSection {U : (Opens X.carrier)ᵒᵖ}
    (x : kernelIdeal Q.thickenedSheafReduction.hom U) : Q.incl (Q.kernelSection x) = x.1 :=
  Classical.choose_spec (Q.exists_incl x.1 (Q.reduction_eq_zero_of_mem_kernelIdeal x))

/-- The kernel section of `x` is the unique section of `i_* 𝒢` whose inclusion is `x`. -/
theorem kernelSection_eq {U : (Opens X.carrier)ᵒᵖ}
    (x : kernelIdeal Q.thickenedSheafReduction.hom U)
    (g : ((modulePushforward Q.i).obj G).val.obj ((Opens.map Q.baseIso.inv).op.obj U))
    (hg : Q.incl g = x.1) : Q.kernelSection x = g :=
  Q.incl_injective ((Q.incl_kernelSection x).trans hg.symm)

/-- The identification of the ideal of the extension attached to a solution with `𝒢`: a kernel
section of the reduction is the image of a unique section of `i_* 𝒢`, read on `U`. -/
def thickenedIdeal : IdealRestriction.{u, u, u, u} Q.thickenedSheafReduction G where
  app U :=
    { toFun := fun x => Q.descendSection (Q.kernelSection x)
      map_zero' := by
        rw [Q.kernelSection_eq 0 0 incl_zero, descendSection_zero]
      map_add' := fun x y => by
        rw [Q.kernelSection_eq (x + y) (Q.kernelSection x + Q.kernelSection y)
          (by rw [incl_add, incl_kernelSection, incl_kernelSection]; rfl), descendSection_add] }
  app_smul U r x := by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Q.kernelSection_eq (r • x)
      ((show Q.X'.presheaf.obj ((Opens.map Q.baseIso.inv).op.obj U) from r) • Q.kernelSection x)
      (by rw [← mul_incl, incl_kernelSection]; rfl), descendSection_smul]
    rfl
  app_map {U V} k x :=
    (congrArg Q.descendSection (Q.kernelSection_eq _ _ (by
      rw [incl_naturality, incl_kernelSection]; rfl))).trans
      (Q.descendSection_naturality k (Q.kernelSection x))

/-- **A solution of Stacks 08U7, read as a square-zero extension of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras on the opens of `X`.**  Its sheaf of rings is `𝒪_{X'}` transported
along the homeomorphism underlying the thickening, its reduction is the comorphism of the
thickening, its algebra structure is the comorphism of `f'`, and its ideal is identified with
`𝒢` through the identification `Ker(i^♯) ≅ i_* 𝒢` of the solution. -/
def toAlgebraExtension : AlgebraSquareZeroExtension (f ≫ t) G where
  sheaf := Q.thickenedSheaf
  base := Q.thickenedSheafBase
  reduction := Q.thickenedSheafReduction
  base_comp_reduction := Q.thickenedSheafBase_comp_reduction
  reduction_surjective := Q.isLocallySurjective_thickenedReduction
  ideal := Q.thickenedIdeal

/-- The identification of the ideal attached to a solution is bijective on sections. -/
theorem thickenedIdeal_bijective (U : (Opens X.carrier)ᵒᵖ) :
    Function.Bijective (Q.thickenedIdeal.app U) := by
  have hround := map_eqToHom_bijective G (congrArg op (Q.opens_roundTrip U.unop))
  constructor
  · intro x y h
    have h₁ : G.val.map (Q.roundTripHom U) (Q.kernelSection x) =
        G.val.map (Q.roundTripHom U) (Q.kernelSection y) := h
    exact Subtype.ext ((Q.incl_kernelSection x).symm.trans
      ((congrArg Q.incl (hround.1 h₁)).trans (Q.incl_kernelSection y)))
  · intro m
    obtain ⟨g, hg⟩ := hround.2 m
    have hx : Q.incl g ∈ kernelIdeal Q.thickenedSheafReduction.hom U := by
      show (Q.thickenedReduction.app U).hom (Q.incl g) = 0
      rw [thickenedReduction_app]
      exact (congrArg _ (Q.reduction_incl g)).trans (map_zero _)
    refine ⟨⟨Q.incl g, hx⟩, ?_⟩
    exact (congrArg (G.val.map (Q.roundTripHom U))
      (Q.kernelSection_eq ⟨Q.incl g, hx⟩ g rfl)).trans hg

/-- The ideal of the square-zero extension attached to a solution is identified with `𝒢`
bijectively on sections. -/
theorem toAlgebraExtension_idealBijective : Q.toAlgebraExtension.IdealBijective :=
  Q.thickenedIdeal_bijective

end DeformationSolution

/-! ### The prescribed map on ideals, on sections of the base -/

section Prescribed

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}

/-- The section of the ideal sheaf `𝒥 = Ker(t^♯)` determined by a section of `𝒪_{S'}` killed by
`t^♯`. -/
def baseIdealSection (t : S ⟶ S') (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) :
    (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V :=
  Classical.choose (Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero t V.unop s hs)

/-- The inclusion of the ideal sheaf `𝒥` into `𝒪_{S'}` sends the section determined by `s` to
`s`. -/
theorem idealSheafι_baseIdealSection (t : S ⟶ S') (V : (Opens S'.carrier)ᵒᵖ)
    (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    (Stacks.ClosedImmersion.idealSheafι t).val.app V (baseIdealSection t V s hs) = s :=
  Classical.choose_spec
    (Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero t V.unop s hs)

/-- The prescribed map `c : f^* t^* 𝒥 ⟶ 𝒢` of **Stacks 08U7**, transposed to a map
`𝒥 ⟶ (f ∘ t)_* 𝒢` of `𝒪_{S'}`-modules along `(f ∘ t)^* ⊣ (f ∘ t)_*` and the identification
`(f ∘ t)^* = f^* t^*`. -/
def prescribedIdealMap
    (c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) :
    AlgebraicGeometry.SheafOfModules.idealSheaf t ⟶ (modulePushforward (f ≫ t)).obj G :=
  (modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _
    ((modulePullbackCompUniq f t).hom.app _ ≫ c)

/-- The value of the prescribed map `c` on a section `s` of `𝒪_{S'}` killed by `t^♯`: a section
of `𝒢` over the preimage of the open of `s` in `X`. -/
def prescribedIdealSection
    (c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    G.val.obj (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) :=
  (prescribedIdealMap c).val.app V (baseIdealSection t V s hs)

end Prescribed



/-! ### The compatibility equation of a solution, transposed to the base -/

section Compatibility

/-- Precomposing with the inverse of the comparison of two left adjoints of one functor
transposes along the second adjunction as the original map does along the first. -/
theorem homEquiv_leftAdjointUniq_inv_app_comp {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {F F' : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj1 : F ⊣ R) (adj2 : F' ⊣ R) (x : C₁) {y : C₂}
    (g : F.obj x ⟶ y) :
    adj2.homEquiv _ _ ((Adjunction.leftAdjointUniq adj1 adj2).inv.app x ≫ g) =
      adj1.homEquiv _ _ g := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp, ← Category.assoc]
  congr 1
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 x, Category.assoc, ← R.map_comp,
    Iso.hom_inv_id_app, R.map_id]
  exact Category.comp_id _

/-- The canonical identification `(f ∘ t)_* M ⟶ f'_* i_* M` attached to a morphism of
thickenings, through `i ≫ f' = f ≫ t`. -/
def MorphismOfThickenings.pushforwardComparison (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X)) :
    (modulePushforward (D.f ≫ D.t)).obj M ⟶
      (modulePushforward D.f').obj ((modulePushforward D.i).obj M) :=
  eqToHom (congrArg (fun m => (modulePushforward m).obj M) D.comm.symm) ≫
    (modulePushforwardCompSymm D.i D.f').hom.app M

/-- The first order reduction `(f')^* 𝒥 ⟶ i_* f^* t^* 𝒥` followed by `i_*` of a map
`c : f^* t^* 𝒥 ⟶ M` transposes, along `(f')^* ⊣ f'_*`, to the transpose of `c` along
`(f ∘ t)^* ⊣ (f ∘ t)_*` read through `pushforwardComparison`. -/
theorem MorphismOfThickenings.homEquiv_firstOrderSurjection_comp_prescribedIdealMap
    (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    {M : SheafOfModules.{u} (structureSheafRing D.X)}
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ M) :
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
        (D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c) =
      prescribedIdealMap (f := D.f) (t := D.t) c ≫ D.pushforwardComparison M := by
  let adjf' := modulePullbackPushforwardAdjunction D.f'
  let adji := modulePullbackPushforwardAdjunction D.i
  let e := modulePushforwardCompSymm D.i D.f'
  let adjseq := (adjf'.comp adji).ofNatIsoRight e.symm
  have h1 : D.firstOrderSurjection hi ht ≫ (modulePushforward D.i).map c =
      adji.homEquiv _ _ (D.reducedPullbackComparison.hom ≫ c) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp]
    rfl
  have h2 : ∀ z : (modulePullback D.i).obj ((modulePullback D.f').obj D.idealJ) ⟶ M,
      adjf'.homEquiv _ _ (adji.homEquiv _ _ z) =
        adjseq.homEquiv _ _ z ≫ e.hom.app M := by
    intro z
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Category.assoc, Iso.symm_hom,
      Iso.inv_hom_id_app, Category.comp_id, Adjunction.comp_homEquiv]
    rfl
  have h3 : ∀ w : (modulePullback (D.i ≫ D.f')).obj D.idealJ ⟶ M,
      adjseq.homEquiv _ _ ((modulePullbackCompUniq D.i D.f').inv.app D.idealJ ≫ w) =
        (modulePullbackPushforwardAdjunction (D.i ≫ D.f')).homEquiv _ _ w :=
    fun w => homEquiv_leftAdjointUniq_inv_app_comp _ adjseq D.idealJ w
  rw [h1, h2, MorphismOfThickenings.reducedPullbackComparison]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Iso.app_hom, Category.assoc]
  rw [h3, homEquiv_eqToHom_comp D.comm D.idealJ, prescribedIdealMap,
    MorphismOfThickenings.pushforwardComparison, Category.assoc]

/-- **The compatibility equation of a solution, transposed to the base.**  For a morphism of
first order thickenings `D`, a map `k : I ⟶ i_* M` out of the ideal of `i` and a map
`c : f^* t^* 𝒥 ⟶ M`, the first order ideal map followed by `k` is `i_* c` exactly when the
canonical ideal map `(f')^* 𝒥 ⟶ I` followed by `k`, transposed to a map `𝒥 ⟶ f'_* i_* M`, is the
transpose of `c` read through `pushforwardComparison`. -/
theorem MorphismOfThickenings.firstOrderIdealMap_comp_eq_iff (D : MorphismOfThickenings.{u})
    (hi : IsFirstOrderThickening D.i) (ht : IsFirstOrderThickening D.t)
    {M : SheafOfModules.{u} (structureSheafRing D.X)}
    (k : D.idealI ⟶ (modulePushforward D.i).obj M)
    (c : (modulePullback D.f).obj ((modulePullback D.t).obj D.idealJ) ⟶ M) :
    (D.firstOrderIdealMap hi ht).1 ≫ k = (modulePushforward D.i).map c ↔
      (modulePullbackPushforwardAdjunction D.f').homEquiv _ _ (D.idealMap.1 ≫ k) =
        prescribedIdealMap (f := D.f) (t := D.t) c ≫ D.pushforwardComparison M := by
  have hepi := D.firstOrderSurjection_epi hi ht
  rw [← D.homEquiv_firstOrderSurjection_comp_prescribedIdealMap hi ht c, Equiv.apply_eq_iff_eq,
    ← cancel_epi (D.firstOrderSurjection hi ht), ← Category.assoc,
    (D.firstOrderIdealMap hi ht).2.1]

/-- On sections, transport along an equality `φ = ψ` of the pushforward of a sheaf of modules is
restriction along the corresponding equality of opens. -/
theorem pushforward_eqToHom_val_app {Y T : RingedSpace.{u, u}} {φ ψ : Y ⟶ T} (h : φ = ψ)
    (M : SheafOfModules.{u} (structureSheafRing Y)) (V : (Opens T.carrier)ᵒᵖ)
    (z : ((modulePushforward φ).obj M).val.obj V) :
    (eqToHom (congrArg (fun m => (modulePushforward m).obj M) h)).val.app V z =
      M.val.map (eqToHom (congrArg (fun m : Y ⟶ T => op ((Opens.map m.hom.base).obj V.unop)) h) :
        op ((Opens.map φ.hom.base).obj V.unop) ⟶ op ((Opens.map ψ.hom.base).obj V.unop)) z := by
  subst h
  simp only [eqToHom_refl, PresheafOfModules.map_id]
  rfl

/-- On sections, `pushforwardComparison` is restriction along the equality of opens given by the
commutative square. -/
theorem MorphismOfThickenings.pushforwardComparison_val_app (D : MorphismOfThickenings.{u})
    (M : SheafOfModules.{u} (structureSheafRing D.X)) (V : (Opens D.S'.carrier)ᵒᵖ)
    (z : ((modulePushforward (D.f ≫ D.t)).obj M).val.obj V) :
    (D.pushforwardComparison M).val.app V z =
      M.val.map (eqToHom (congrArg (fun m : D.X ⟶ D.S' => op ((Opens.map m.hom.base).obj V.unop))
          D.comm.symm) :
        op ((Opens.map (D.f ≫ D.t).hom.base).obj V.unop) ⟶
          op ((Opens.map (D.i ≫ D.f').hom.base).obj V.unop)) z :=
  pushforward_eqToHom_val_app D.comm.symm M V z

/-- Two composites of restriction maps of a presheaf of modules between the same opens agree. -/
theorem map_map_eq_map {Y : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing Y))
    {A B C' : (Opens Y.carrier)ᵒᵖ} (k₁ : A ⟶ B) (k₂ : B ⟶ C') (k : A ⟶ C') (x : M.val.obj A) :
    M.val.map k₂ (M.val.map k₁ x) = M.val.map k x := by
  rw [← PresheafOfModules.map_comp_apply]
  exact M.val.congr_map_apply (Subsingleton.elim _ _) x

/-- Restriction along an endomorphism of an open is the identity. -/
theorem map_self_eq {Y : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing Y))
    {A : (Opens Y.carrier)ᵒᵖ} (k : A ⟶ A) (x : M.val.obj A) : M.val.map k x = x := by
  rw [M.val.congr_map_apply (Subsingleton.elim k (𝟙 A)) x, PresheafOfModules.map_id]
  rfl

/-- Restricting around a loop of opens is the identity. -/
theorem map_map_map_eq_self {Y : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Y)) {A B C' : (Opens Y.carrier)ᵒᵖ}
    (k₁ : A ⟶ B) (k₂ : B ⟶ C') (k₃ : C' ⟶ A) (x : M.val.obj A) :
    M.val.map k₃ (M.val.map k₂ (M.val.map k₁ x)) = x := by
  rw [map_map_eq_map M k₁ k₂ (k₁ ≫ k₂), map_map_eq_map M _ k₃ (𝟙 A), map_self_eq]

end Compatibility

/-! ### The prescribed map on the extension attached to a solution -/

/-- Transposing the canonical ideal map `(f')^* 𝒥 ⟶ I` of a morphism of thickenings followed by a
map `κ` out of `I` which composes with `ι` to the inclusion of `I` gives, after `ι`, the inclusion
of `𝒥` followed by the comorphism of `f'`. -/
private theorem homEquiv_idealMap_comp_map_comp {D : MorphismOfThickenings.{u}}
    {N : SheafOfModules.{u} (structureSheafRing D.X')} (κ : D.idealI ⟶ N)
    (ι : N ⟶ SheafOfModules.unit (structureSheafRing D.X'))
    (h : κ ≫ ι = kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i))) :
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _ (D.idealMap.1 ≫ κ) ≫
        (modulePushforward D.f').map ι =
      Stacks.ClosedImmersion.idealSheafι D.t ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.f') :=
  ((modulePullbackPushforwardAdjunction D.f').homEquiv_naturality_right _ _).symm.trans
    ((congrArg ((modulePullbackPushforwardAdjunction D.f').homEquiv _ _)
      ((Category.assoc _ _ _).trans ((congrArg (D.idealMap.1 ≫ ·) h).trans D.idealMap.2))).trans
      (homEquiv_map_comp_pullbackUnitToUnit D.f' _ _))

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-- The canonical ideal map of a solution followed by the identification of its ideal with
`𝒢`, transposed to a map `𝒥 ⟶ f'_* i_* 𝒢` of `𝒪_{S'}`-modules. -/
def idealMapTranspose :
    AlgebraicGeometry.SheafOfModules.idealSheaf t ⟶
      (modulePushforward Q.f').obj ((modulePushforward Q.i).obj G) :=
  (modulePullbackPushforwardAdjunction Q.f').homEquiv _ _
    (Q.toMorphismOfThickenings.idealMap.1 ≫ Q.kernelIso.hom)

/-- The transposed ideal map of a solution followed by the inclusion of `𝒢` as the ideal is the
inclusion of `𝒥` followed by the comorphism of `f'`. -/
theorem idealMapTranspose_comp_idealInclusion :
    Q.idealMapTranspose ≫ (modulePushforward Q.f').map Q.idealInclusion =
      Stacks.ClosedImmersion.idealSheafι t ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom Q.f') := by
  exact homEquiv_idealMap_comp_map_comp (D := Q.toMorphismOfThickenings) _ _
    (Iso.hom_inv_id_assoc Q.kernelIso (kernel.ι Q.structureMap))

/-- `idealMapTranspose_comp_idealInclusion`, on sections. -/
theorem incl_idealMapTranspose (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    Q.incl (Q.idealMapTranspose.val.app V y) =
      (Q.f'.hom.c.app V).hom ((Stacks.ClosedImmersion.idealSheafι t).val.app V y) :=
  congrArg (fun k => (k.val.app V).hom y) Q.idealMapTranspose_comp_idealInclusion

/-- The compatibility equation of a solution, transposed: the transposed ideal map is the
transposed prescribed map. -/
theorem idealMapTranspose_eq :
    Q.idealMapTranspose =
      prescribedIdealMap c ≫ Q.toMorphismOfThickenings.pushforwardComparison G :=
  (Q.toMorphismOfThickenings.firstOrderIdealMap_comp_eq_iff Q.i_firstOrder ht Q.kernelIso.hom
    c).1 Q.compatibility

/-- **The ideal map of the extension attached to a solution is the prescribed one.**  A section
`s` of `𝒪_{S'}` killed by `t^♯` is carried by the algebra structure of the extension into the
square-zero ideal, and there its section of `𝒢` is the value of the prescribed map `c` on `s`.
This is the compatibility equation of the solution, read on sections of `S'`. -/
theorem thickenedIdeal_deformedBasePresheafMap (V : (Opens S'.carrier)ᵒᵖ)
    (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0)
    (hmem : (Q.deformedBasePresheafMap.app V).hom s ∈
      kernelIdeal Q.thickenedSheafReduction.hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop))) :
    Q.thickenedIdeal.app _ ⟨(Q.deformedBasePresheafMap.app V).hom s, hmem⟩ =
      prescribedIdealSection c V s hs := by
  set y := baseIdealSection t V s hs with hy
  have hz : Q.incl (Q.idealMapTranspose.val.app V y) = (Q.f'.hom.c.app V).hom s := by
    rw [incl_idealMapTranspose, hy, idealSheafι_baseIdealSection]
  have hks : Q.kernelSection ⟨(Q.deformedBasePresheafMap.app V).hom s, hmem⟩ =
      ((modulePushforward Q.i).obj G).val.map
        (eqToHom (congrArg op (Q.opens_map_f' V.unop))) (Q.idealMapTranspose.val.app V y) :=
    Q.kernelSection_eq _ _ ((Q.incl_naturality _ _).trans
      (congrArg (Q.X'.presheaf.map (eqToHom (congrArg op (Q.opens_map_f' V.unop)))).hom hz))
  have hval : Q.idealMapTranspose.val.app V y =
      G.val.map (eqToHom (congrArg (fun m : X ⟶ S' => op ((Opens.map m.hom.base).obj V.unop))
          Q.comm.symm)) ((prescribedIdealMap c).val.app V y) := by
    rw [Q.idealMapTranspose_eq]
    exact Q.toMorphismOfThickenings.pushforwardComparison_val_app G V _
  show Q.descendSection (Q.kernelSection _) = (prescribedIdealMap c).val.app V y
  rw [hks, hval]
  exact map_map_map_eq_self G _ _ _ _

end DeformationSolution

namespace AlgebraSquareZeroExtension

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- The adjoint of the algebra structure of an extension followed by the reduction is the
comorphism of `f ∘ t`. -/
theorem adjointBase_comp_reduction (P : AlgebraSquareZeroExtension (f ≫ t) G) :
    P.adjointBase ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map P.reduction =
      ObjectProperty.homMk (f ≫ t).hom.c :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv_naturality_right P.base P.reduction).symm.trans
    ((congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv _ _) P.base_comp_reduction).trans (Equiv.apply_symm_apply _ _))

/-- A section of `𝒪_{S'}` killed by `t^♯` is carried by the algebra structure of an extension of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras into the square-zero ideal. -/
theorem adjointBase_mem_kernelIdeal (P : AlgebraSquareZeroExtension (f ≫ t) G)
    (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0) :
    (P.adjointBase.hom.app V).hom s ∈
      kernelIdeal P.reduction.hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) := by
  have h := congrArg (fun k => (k.hom.app V).hom s) P.adjointBase_comp_reduction
  change (P.reduction.hom.app _).hom ((P.adjointBase.hom.app V).hom s) =
    (f.hom.c.app _).hom ((t.hom.c.app V).hom s) at h
  rw [hs, map_zero] at h
  exact h

end AlgebraSquareZeroExtension

namespace DeformationSolution

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t}
  {f : X ⟶ S} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-- **The extension attached to a solution induces the prescribed map on ideals.**  For a
section `s` of `𝒪_{S'}` killed by `t^♯`, the section of `𝒢` that the algebra structure of
`toAlgebraExtension Q` carries `s` to is the value of `c` on `s`. -/
theorem toAlgebraExtension_ideal_adjointBase (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) :
    Q.toAlgebraExtension.ideal.app _
        ⟨(Q.toAlgebraExtension.adjointBase.hom.app V).hom s,
          Q.toAlgebraExtension.adjointBase_mem_kernelIdeal V s hs⟩ =
      prescribedIdealSection c V s hs := by
  have hb : Q.toAlgebraExtension.adjointBase = Q.deformedBaseSheafMap :=
    Q.adjoint_thickenedSheafBase
  have hx : (Q.toAlgebraExtension.adjointBase.hom.app V).hom s =
      (Q.deformedBasePresheafMap.app V).hom s := congrArg (fun k => (k.hom.app V).hom s) hb
  have hmem : (Q.deformedBasePresheafMap.app V).hom s ∈
      kernelIdeal Q.thickenedSheafReduction.hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) :=
    hx ▸ Q.toAlgebraExtension.adjointBase_mem_kernelIdeal V s hs
  refine Eq.trans ?_ (Q.thickenedIdeal_deformedBasePresheafMap V s hs hmem)
  exact congrArg (Q.thickenedIdeal.app _) (Subtype.ext hx)

end DeformationSolution


/-! ### A square-zero extension on `X` read as a solution -/

namespace AlgebraSquareZeroExtension

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension (f ≫ t) G)

/-- The ringed space `(X, 𝒪_{X'})` of a square-zero extension of sheaves of rings on `X`. -/
def space : RingedSpace.{u, u} where
  carrier := X.carrier
  presheaf := P.sheaf.obj
  IsSheaf := P.sheaf.property

/-- The thickening `X ⟶ (X, 𝒪_{X'})`: the identity on the space and the reduction on structure
sheaves. -/
def thickening : X ⟶ P.space :=
  ⟨{ base := 𝟙 X.carrier, c := P.reduction.hom }⟩

/-- The morphism `(X, 𝒪_{X'}) ⟶ S'` whose comorphism is the adjoint of the algebra structure. -/
def over : P.space ⟶ S' :=
  ⟨{ base := (f ≫ t).hom.base, c := P.adjointBase.hom }⟩

/-- The thickening followed by the structure morphism is `f ∘ t`. -/
theorem thickening_comp_over : P.thickening ≫ P.over = f ≫ t := by
  have h := congrArg (fun k => k.hom) P.adjointBase_comp_reduction
  refine InducedCategory.hom_ext (PresheafedSpace.ext _ _ (Category.id_comp _) ?_)
  refine NatTrans.ext (funext fun V => ?_)
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, eqToHom_map]
  have hV := congrArg (fun k => k.app V) h
  exact (congrArg (· ≫ _) hV).trans (Category.comp_id _)

/-- The comorphism of the thickening is locally surjective. -/
theorem isLocallySurjective_thickening :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology P.space.carrier)
      (structureSheafHom P.thickening).hom :=
  ⟨fun s => P.reduction_surjective.imageSieve_mem s⟩

/-- A map into `𝒪_{X'}` killed by the reduction lands in its kernel ideal, on sections. -/
theorem mem_kernelIdeal_of_comp_eq_zero {W : SheafOfModules.{u} (structureSheafRing P.space)}
    (k : W ⟶ SheafOfModules.unit (structureSheafRing P.space))
    (hk : k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening) = 0)
    (U : (Opens X.carrier)ᵒᵖ) (w : W.val.obj U) :
    (k.val.app U).hom w ∈ kernelIdeal P.reduction.hom U :=
  congrArg (fun φ : W ⟶ (modulePushforward P.thickening).obj
    (SheafOfModules.unit (structureSheafRing X)) => (φ.val.app U).hom w) hk

/-- The factorization through `𝒢` of a map into `𝒪_{X'}` killed by the reduction. -/
def idealLift {W : SheafOfModules.{u} (structureSheafRing P.space)}
    (k : W ⟶ SheafOfModules.unit (structureSheafRing P.space))
    (hk : k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening) = 0) :
    W ⟶ (modulePushforward P.thickening).obj G where
  val :=
    { app := fun U => ConcreteCategory.ofHom
        { toFun := fun w => P.ideal.app U ⟨(k.val.app U).hom w,
            P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩
          map_add' := fun w w' =>
            (congrArg (P.ideal.app U) (Subtype.ext (map_add _ _ _))).trans
              (map_add (P.ideal.app U) _ _)
          map_smul' := fun r w => by
            have h : (⟨(k.val.app U).hom (r • w), P.mem_kernelIdeal_of_comp_eq_zero k hk U _⟩ :
                ↥(kernelIdeal P.reduction.hom U)) =
                (show P.sheaf.obj.obj U from r) •
                  ⟨(k.val.app U).hom w, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩ :=
              Subtype.ext (map_smul (k.val.app U).hom r w)
            exact (congrArg (P.ideal.app U) h).trans (P.ideal.app_smul U _ _) }
      naturality := fun {U V} j => by
        ext w
        refine Eq.trans ?_ (P.ideal.app_map j
          ⟨(k.val.app U).hom w, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩)
        exact congrArg (P.ideal.app V)
          (Subtype.ext (PresheafOfModules.naturality_apply k.val j w)) }

/-- On sections, the lift of `k` through the ideal is the identification of the ideal applied to
the value of `k`. -/
theorem idealLift_app {W : SheafOfModules.{u} (structureSheafRing P.space)}
    (k : W ⟶ SheafOfModules.unit (structureSheafRing P.space))
    (hk : k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening) = 0)
    (U : (Opens X.carrier)ᵒᵖ) (w : W.val.obj U) :
    ((P.idealLift k hk).val.app U).hom w =
      P.ideal.app U ⟨(k.val.app U).hom w, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩ :=
  rfl

variable {P}
variable (hP : P.IdealBijective)
include hP

/-- Two local sections of `𝒪_{X'}` killed by the reduction multiply to zero. -/
theorem mul_eq_zero_of_reduction_eq_zero (U : (Opens X.carrier)ᵒᵖ)
    (a b : P.sheaf.obj.obj U) (ha : (P.reduction.hom.app U).hom a = 0)
    (hb : (P.reduction.hom.app U).hom b = 0) : a * b = 0 :=
  (congrArg₂ (· * ·) (P.idealIncl_ideal hP U ⟨a, ha⟩).symm
    (P.idealIncl_ideal hP U ⟨b, hb⟩).symm).trans (P.idealIncl_mul_idealIncl hP U _ _)

/-- **The thickening of a square-zero extension with bijective ideal is a first order
thickening.** -/
theorem isFirstOrderThickening_thickening : IsFirstOrderThickening P.thickening := by
  refine ⟨⟨?_, ?_, ?_⟩, fun U => ?_⟩
  · show IsIso (𝟙 X.carrier)
    infer_instance
  · have h : Presheaf.IsLocallySurjective (Opens.grothendieckTopology P.space.carrier)
        ((PresheafOfModules.toPresheaf _).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening)).val) :=
      ⟨fun s => P.isLocallySurjective_thickening.imageSieve_mem s⟩
    have h2 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening))) := h
    exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance
  · intro U a ha x hx
    refine ⟨U, le_rfl, hx, 2, ?_⟩
    have hid : ((structureSheafRing P.space).obj.map (homOfLE (le_rfl (a := U))).op) a = a := by
      rw [show (homOfLE (le_rfl (a := U))).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
      rfl
    rw [hid, pow_two]
    exact mul_eq_zero_of_reduction_eq_zero hP (op U) a a ha ha
  · rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one]
    refine le_antisymm (Ideal.mul_le.2 ?_) bot_le
    intro r hr s hs
    rw [Ideal.mem_bot]
    exact mul_eq_zero_of_reduction_eq_zero hP (op U) r s hr hs

/-- The inclusion `𝒢 ⟶ 𝒪_{X'}` of a square-zero extension with bijective ideal, as a map of
sheaves of `𝒪_{X'}`-modules out of the pushforward of `𝒢` along the thickening. -/
def idealInclHom :
    (modulePushforward P.thickening).obj G ⟶ SheafOfModules.unit (structureSheafRing P.space) where
  val :=
    { app := fun U => ConcreteCategory.ofHom
        { toFun := fun g => P.idealIncl hP U g
          map_add' := fun g h => P.idealIncl_add hP U g h
          map_smul' := fun r g => (P.mul_idealIncl hP U r g).symm }
      naturality := fun {U V} k => by
        ext g
        exact P.idealIncl_map hP k g }

/-- On sections, `idealInclHom` is the inclusion `idealIncl` of `𝒢` into `𝒪_{X'}`. -/
theorem idealInclHom_app (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) :
    ((idealInclHom hP).val.app U).hom g = P.idealIncl hP U g :=
  rfl

/-- The inclusion of `𝒢` is killed by the reduction. -/
theorem idealInclHom_comp :
    idealInclHom hP ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening) =
      0 := by
  ext U g
  exact P.reduction_idealIncl hP U g

/-- **The inclusion of `𝒢` is a kernel of the reduction.** -/
def isLimitIdealInclHom :
    IsLimit (KernelFork.ofι (idealInclHom hP) (idealInclHom_comp hP)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => P.idealLift k hk)
    (fun {W} k hk => by
      ext U w
      exact P.idealIncl_ideal hP U
        ⟨(k.val.app U).hom w, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩)
    (fun {W} k hk m hm => by
      ext U w
      have h := congrArg (fun φ : W ⟶ SheafOfModules.unit (structureSheafRing P.space) =>
        (φ.val.app U).hom w) hm
      change P.idealIncl hP U ((m.val.app U).hom w) = (k.val.app U).hom w at h
      change (m.val.app U).hom w = P.ideal.app U _
      rw [← P.ideal_idealIncl hP U ((m.val.app U).hom w)]
      exact congrArg (P.ideal.app U) (Subtype.ext h))

/-- The identification of the ideal of the thickening with `𝒢`. -/
def thickeningKernelIso :
    AlgebraicGeometry.SheafOfModules.idealSheaf P.thickening ≅
      (modulePushforward P.thickening).obj G :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitIdealInclHom hP)

/-- The identification of the ideal followed by the inclusion of `𝒢` is the inclusion of the
ideal. -/
theorem thickeningKernelIso_hom_comp_idealInclHom :
    (thickeningKernelIso hP).hom ≫ idealInclHom hP = kernel.ι _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (isLimitIdealInclHom hP)
    WalkingParallelPair.zero

/-- The morphism of first order thickenings `(X ⟶ (X, 𝒪_{X'})) ⟶ (S ⟶ S')` of a square-zero
extension with bijective ideal. -/
def morphismOfThickenings (ht : IsFirstOrderThickening t) : MorphismOfThickenings.{u} where
  X := X
  X' := P.space
  S := S
  S' := S'
  i := P.thickening
  t := t
  f := f
  f' := P.over
  i_isThickening := (isFirstOrderThickening_thickening hP).1
  t_isThickening := ht.1
  comm := P.thickening_comp_over

variable {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-- The transposed ideal map of the thickening of an extension satisfying the condition of the
prescribed map is the transposed prescribed map. -/
theorem homEquiv_idealMap_comp_thickeningKernelIso (ht : IsFirstOrderThickening t)
    (hc : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0),
      P.ideal.app _ ⟨(P.adjointBase.hom.app V).hom s, P.adjointBase_mem_kernelIdeal V s hs⟩ =
        prescribedIdealSection c V s hs) :
    (modulePullbackPushforwardAdjunction P.over).homEquiv _ _
        ((morphismOfThickenings hP ht).idealMap.1 ≫ (thickeningKernelIso hP).hom) =
      prescribedIdealMap c ≫ (morphismOfThickenings hP ht).pushforwardComparison G := by
  set D := morphismOfThickenings hP ht with hD
  set L := (modulePullbackPushforwardAdjunction P.over).homEquiv _ _
    (D.idealMap.1 ≫ (thickeningKernelIso hP).hom) with hL
  have hincl : L ≫ (modulePushforward P.over).map (idealInclHom hP) =
      Stacks.ClosedImmersion.idealSheafι t ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.over) :=
    homEquiv_idealMap_comp_map_comp (D := D) _ _ (thickeningKernelIso_hom_comp_idealInclHom hP)
  ext V y
  set s := (Stacks.ClosedImmersion.idealSheafι t).val.app V y with hsdef
  have hs : (t.hom.c.app V).hom s = 0 :=
    congrArg (fun k => (k.val.app V).hom y)
      (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom t)))
  have hy : y = baseIdealSection t V s hs :=
    Stacks.ClosedImmersion.injective_idealSheafι_val_app t V.unop
      (idealSheafι_baseIdealSection t V s hs).symm
  have hLy : P.idealIncl hP _ ((L.val.app V).hom y) = (P.adjointBase.hom.app V).hom s :=
    congrArg (fun k => (k.val.app V).hom y) hincl
  have hLy' : (L.val.app V).hom y = prescribedIdealSection c V s hs := by
    rw [← hc V s hs, ← P.ideal_idealIncl hP _ ((L.val.app V).hom y)]
    exact congrArg (P.ideal.app _) (Subtype.ext hLy)
  refine hLy'.trans ?_
  show (prescribedIdealMap c).val.app V (baseIdealSection t V s hs) =
    (D.pushforwardComparison G).val.app V ((prescribedIdealMap c).val.app V y)
  exact (congrArg ((prescribedIdealMap c).val.app V).hom hy.symm).trans
    ((map_self_eq G _ _).symm.trans (D.pushforwardComparison_val_app G V _).symm)

/-- **A square-zero extension on `X` with bijective ideal which induces the prescribed map `c` on
ideals is a solution of Stacks 08U7.** The deformed space is `(X, 𝒪_{X'})`, the thickening is
the reduction, the morphism to `S'` is the adjoint of the algebra structure, and the ideal of the
thickening is `𝒢` through the bijective identification. -/
def toDeformationSolution (ht : IsFirstOrderThickening t)
    (hc : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0),
      P.ideal.app _ ⟨(P.adjointBase.hom.app V).hom s, P.adjointBase_mem_kernelIdeal V s hs⟩ =
        prescribedIdealSection c V s hs) :
    DeformationSolution t ht f G c where
  X' := P.space
  i := P.thickening
  f' := P.over
  i_firstOrder := isFirstOrderThickening_thickening hP
  comm := P.thickening_comp_over
  kernelIso := thickeningKernelIso hP
  compatibility := by
    intro D
    exact ((morphismOfThickenings hP ht).firstOrderIdealMap_comp_eq_iff
      (isFirstOrderThickening_thickening hP) ht (thickeningKernelIso hP).hom c).2
      (homEquiv_idealMap_comp_thickeningKernelIso hP ht hc)

variable (ht : IsFirstOrderThickening t)
  (hc : ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0),
      P.ideal.app _ ⟨(P.adjointBase.hom.app V).hom s, P.adjointBase_mem_kernelIdeal V s hs⟩ =
        prescribedIdealSection c V s hs)

/-- The homeomorphism underlying the thickening of an extension is the identity. -/
theorem baseIso_inv_toDeformationSolution :
    (toDeformationSolution hP ht hc).baseIso.inv = 𝟙 X.carrier :=
  (Category.id_comp _).symm.trans (toDeformationSolution hP ht hc).baseIso.hom_inv_id

/-- The opens of `X` are unchanged by the inverse of the homeomorphism underlying the thickening of
an extension: that homeomorphism is the identity. -/
theorem opens_map_baseIso_inv (U : Opens X.carrier) :
    (Opens.map (toDeformationSolution hP ht hc).baseIso.inv).obj U = U :=
  (congrArg (fun m : X.carrier ⟶ X.carrier => (Opens.map m).obj U)
    (baseIso_inv_toDeformationSolution hP ht hc)).trans rfl

/-- The restriction of `𝒪_{X'}` along the equality of opens of `opens_map_baseIso_inv`. -/
abbrev comparisonApp (U : (Opens X.carrier)ᵒᵖ) :
    P.sheaf.obj.obj U ⟶
      P.sheaf.obj.obj (op ((Opens.map (toDeformationSolution hP ht hc).baseIso.inv).obj U.unop)) :=
  P.sheaf.obj.map (eqToHom (congrArg op (opens_map_baseIso_inv hP ht hc U.unop)).symm)

/-- The comparison of an extension with the extension of the solution it defines: restriction
along the equality of opens of `opens_map_baseIso_inv`. -/
def toAlgebraExtensionComparison :
    P.sheaf ⟶ (toDeformationSolution hP ht hc).toAlgebraExtension.sheaf :=
  ObjectProperty.homMk
    { app := fun U => comparisonApp hP ht hc U
      naturality := fun {_ _} _ =>
        (P.sheaf.obj.map_comp _ _).symm.trans
          ((congrArg P.sheaf.obj.map (Subsingleton.elim _ _)).trans
            (P.sheaf.obj.map_comp _ _)) }

/-- The comparison is compatible with the reductions. -/
theorem toAlgebraExtensionComparison_comp_reduction :
    toAlgebraExtensionComparison hP ht hc ≫
        (toDeformationSolution hP ht hc).toAlgebraExtension.reduction = P.reduction := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  have hr := (toDeformationSolution hP ht hc).pushforwardRoundTrip_hom_app U
  have h1 := P.reduction.hom.naturality
    (eqToHom (congrArg op (opens_map_baseIso_inv hP ht hc U.unop)).symm)
  refine (congrArg (fun m => comparisonApp hP ht hc U ≫ P.reduction.hom.app _ ≫ m) hr).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (P.reduction.hom.app U ≫ ·) ((X.presheaf.map_comp _ _).symm.trans
    ((congrArg X.presheaf.map (Subsingleton.elim _ (𝟙 U))).trans (X.presheaf.map_id U)))).trans ?_
  exact Category.comp_id _

/-- The comparison is compatible with the algebra structures. -/
theorem base_comp_toAlgebraExtensionComparison :
    P.base ≫ toAlgebraExtensionComparison hP ht hc =
      (toDeformationSolution hP ht hc).toAlgebraExtension.base := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t).hom.base).homEquiv _ _).injective ?_
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (f ≫ t).hom.base).homEquiv_naturality_right P.base _).trans ?_
  refine Eq.trans ?_ (DeformationSolution.adjoint_thickenedSheafBase _).symm
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  rfl

/-- The comparison is compatible with the identifications of the ideals with `𝒢`. -/
theorem ideal_toAlgebraExtensionComparison (V : (Opens X.carrier)ᵒᵖ)
    (y : ↥(kernelIdeal P.reduction.hom V)) :
    (toDeformationSolution hP ht hc).toAlgebraExtension.ideal.app V
        ⟨((toAlgebraExtensionComparison hP ht hc).hom.app V).hom y,
          kernelIdeal_le_comap P.reduction.hom _ (toAlgebraExtensionComparison hP ht hc).hom
            (hom_of_comp_eq (toAlgebraExtensionComparison_comp_reduction hP ht hc)) V y.2⟩ =
      P.ideal.app V y := by
  set Q := toDeformationSolution hP ht hc
  have hincl : Q.idealInclusion = idealInclHom hP :=
    (congrArg ((thickeningKernelIso hP).inv ≫ ·)
      (thickeningKernelIso_hom_comp_idealInclHom hP).symm).trans (Iso.inv_hom_id_assoc _ _)
  set e := eqToHom (congrArg op (opens_map_baseIso_inv hP ht hc V.unop)).symm
  have hks : Q.kernelSection ⟨((toAlgebraExtensionComparison hP ht hc).hom.app V).hom y,
      kernelIdeal_le_comap P.reduction.hom _ (toAlgebraExtensionComparison hP ht hc).hom
        (hom_of_comp_eq (toAlgebraExtensionComparison_comp_reduction hP ht hc)) V y.2⟩ =
      G.val.map e (P.ideal.app V y) :=
    Q.kernelSection_eq _ _
      ((congrArg (fun φ => (φ.val.app ((Opens.map Q.baseIso.inv).op.obj V)).hom
          (G.val.map e (P.ideal.app V y))) hincl).trans
        ((P.idealIncl_map hP e _).trans
          (congrArg (P.sheaf.obj.map e).hom (P.idealIncl_ideal hP V y))))
  exact (congrArg Q.descendSection hks).trans
    ((map_map_eq_map G e (Q.roundTripHom V) (𝟙 V) (P.ideal.app V y)).trans
      (map_self_eq G (𝟙 V) (P.ideal.app V y)))

/-- **The extension attached to the solution defined by an extension receives a compatible map
from it.** Together with `toDeformationSolution`, this says that a square-zero extension of
`(f ∘ t)⁻¹𝒪_{S'}`-algebras with bijective ideal which induces `c` on ideals is, up to a
compatible map, the extension of a solution. -/
theorem exists_hom_toAlgebraExtension_toDeformationSolution :
    ∃ (θ : P.sheaf ⟶ (toDeformationSolution hP ht hc).toAlgebraExtension.sheaf)
      (_ : P.base ≫ θ = (toDeformationSolution hP ht hc).toAlgebraExtension.base)
      (hred : θ ≫ (toDeformationSolution hP ht hc).toAlgebraExtension.reduction = P.reduction),
      ∀ (V : (Opens X.carrier)ᵒᵖ) (y : ↥(kernelIdeal P.reduction.hom V)),
        (toDeformationSolution hP ht hc).toAlgebraExtension.ideal.app V
          ⟨θ.hom.app V y, kernelIdeal_le_comap P.reduction.hom _ θ.hom (hom_of_comp_eq hred) V
            y.2⟩ = P.ideal.app V y :=
  ⟨toAlgebraExtensionComparison hP ht hc, base_comp_toAlgebraExtensionComparison hP ht hc,
    toAlgebraExtensionComparison_comp_reduction hP ht hc,
    ideal_toAlgebraExtensionComparison hP ht hc⟩

end AlgebraSquareZeroExtension

end AlgebraicGeometry.RingedSpaceThickening

end
