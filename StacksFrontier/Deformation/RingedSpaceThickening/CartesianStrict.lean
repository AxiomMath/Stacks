module

public import StacksFrontier.Deformation.RingedSpaceThickening.StrictCartesian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian squares of thickenings are strict (Stacks 08L2)

Let

    X  ⟶  X'
    ↓f    ↓f'
    S  ⟶  S'

be a morphism of thickenings of ringed spaces (**Stacks 08KZ**).
`StacksFrontier.Deformation.RingedSpaceThickening.StrictCartesian` proves that a *strict* square —
one whose canonical map `(f')^* J ⟶ I` of **Stacks 08L1** is surjective — is cartesian in the
category of ringed spaces. This file proves the converse, and records the equivalence, which is
the whole of **Stacks 08L2**.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.isStrict_of_isPullback`:
  **Stacks 08L2**, a cartesian square of thickenings is strict.
* `AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings.isStrict_iff_isPullback`:
  **Stacks 08L2**, the two conditions are equivalent.

## Implementation notes

The source omits the proof. The implication proved here is the one that needs a test object, and
the test objects used are the one-point ringed spaces of
`Stacks.AssociatedSheaf.coefficientPoint`: for a point `x` of `X'` let `𝔞_x` be the ideal of
`𝒪_{X',x}` of germs at `x` of sections in the range of the ambient ideal map
`(f')^* J ⟶ 𝒪_{X'}`, and let `Z = ({x}, 𝒪_{X',x}/𝔞_x)`. The germ map followed by the quotient
map is a morphism `g : Z ⟶ X'` (`Stacks.AssociatedSheaf.fromCoefficientPointOfHom`), and its
comorphism kills `J`, because a section of `J` is carried by `(f')^♯` into the range of the
ambient ideal map — that is the unit of `(f')^* ⊣ (f')_*` read on sections. So `g ≫ f'` factors
through the thickening `t` by `exists_factorization_of_comp_idealι_eq_zero`, and the square,
being cartesian, lifts `g` to `l : Z ⟶ X`. Now `l ≫ i = g` forces the comorphism of `g` to kill
the ideal `I = ker(i^♯)`, that is `𝔞_x` contains the germ at `x` of every section of `I`. As `x`
is arbitrary, every section of `I` is locally in the range of the ambient ideal map, which is
surjectivity of `(f')^* J ⟶ I` by
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`.

Only the quotient of one *stalk* is needed, never the quotient of the structure sheaf: the
one-point test objects see exactly as much as the fibre product does, because surjectivity of a
map of sheaves of modules is a local — indeed stalkwise — condition.

## References

* [Stacks Project, Tag 08L2](https://stacks.math.columbia.edu/tag/08L2)
* [Stacks Project, Tag 08L1](https://stacks.math.columbia.edu/tag/08L1)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open RingedSpaceModuleAdjunction
open StalkSkyscraperPresheafAdjunctionAuxs

universe u

namespace Stacks.AssociatedSheaf

attribute [local instance] Classical.propDecidable
attribute [local instance] Stacks.AssociatedSheaf.pointMemDecidable
attribute [local implicit_reducible] coefficientPoint

/-- An element is killed by a map followed by an isomorphism exactly when the map kills it. -/
theorem comp_isIso_apply_eq_zero_iff {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    [IsIso g] (a : A) : (f ≫ g) a = 0 ↔ f a = 0 := by
  rw [ConcreteCategory.comp_apply]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h2 : (inv g) (g (f a)) = (inv g) 0 := congrArg (ConcreteCategory.hom (inv g)) h
  rwa [← ConcreteCategory.comp_apply, IsIso.hom_inv_id, ConcreteCategory.id_apply, map_zero] at h2

/-- The sections of a skyscraper presheaf on an open containing the point. -/
def skyscraperObjIsoAt {X : TopCat.{u}} (x : X) (R : CommRingCat.{u}) {U : Opens X}
    (h : x ∈ U) : (skyscraperPresheaf x R).obj (op U) ≅ R :=
  eqToIso (by rw [skyscraperPresheaf_obj, unop_op, ite_eq_left h])

/-- On an open containing the point, the unit of the stalk-skyscraper adjunction is the germ map
followed by the given map out of the stalk. -/
theorem toSkyscraperPresheaf_app_of_mem {X : TopCat.{u}} (x : X)
    (F : TopCat.Presheaf CommRingCat.{u} X) {R : CommRingCat.{u}} (θ : F.stalk x ⟶ R)
    {U : Opens X} (h : x ∈ U) :
    (toSkyscraperPresheaf x θ).app (op U) =
      F.germ U x h ≫ θ ≫ (skyscraperObjIsoAt x R h).inv :=
  dite_eq_left h

/-- **A point of a ringed space with prescribed coefficients.** The morphism

`({x}, R) ⟶ (X, 𝒪_X)`

determined by a ring map `θ : 𝒪_{X,x} ⟶ R`: the underlying map sends the point to `x` and the
comorphism is the germ map at `x` followed by `θ`. At `θ = 𝟙` this is
`Stacks.AssociatedSheaf.fromCoefficientPoint`. -/
def fromCoefficientPointOfHom (X : RingedSpace.{u, u}) (x : X.carrier) {R : CommRingCat.{u}}
    (θ : X.presheaf.stalk x ⟶ R) : coefficientPoint R ⟶ X :=
  { hom :=
    { base := TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1}) x)
      c := toSkyscraperPresheaf x θ ≫ eqToHom (skyscraperPresheaf_eq_pushforward x R) } }

/-- A section over an open neighbourhood of `x` is killed by the comorphism of
`fromCoefficientPointOfHom` exactly when `θ` kills its germ at `x`. This pins the morphism down
as far as the arguments below need it. -/
theorem fromCoefficientPointOfHom_c_app_eq_zero_iff (X : RingedSpace.{u, u}) (x : X.carrier)
    {R : CommRingCat.{u}} (θ : X.presheaf.stalk x ⟶ R) {U : Opens X.carrier} (hx : x ∈ U)
    (a : X.presheaf.obj (op U)) :
    (fromCoefficientPointOfHom X x θ).hom.c.app (op U) a = 0 ↔
      θ (X.presheaf.germ U x hx a) = 0 := by
  let e : R ≅ _ := (skyscraperObjIsoAt x R hx).symm ≪≫
    asIso ((eqToHom (skyscraperPresheaf_eq_pushforward x R)).app (op U))
  have h1 : (fromCoefficientPointOfHom X x θ).hom.c.app (op U) =
      (X.presheaf.germ U x hx ≫ θ) ≫ e.hom := by
    change (toSkyscraperPresheaf x θ).app (op U) ≫ _ = _
    rw [toSkyscraperPresheaf_app_of_mem x X.presheaf θ hx]
    simp only [Category.assoc, e, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [h1]
  exact comp_isIso_apply_eq_zero_iff _ e.hom a

end Stacks.AssociatedSheaf

namespace AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings

attribute [local implicit_reducible] RingedSpaceModuleAdjunction.modulePushforward
  RingedSpaceModuleAdjunction.modulePullback

variable (D : MorphismOfThickenings.{u})

/-! ### The germs of the range of the ambient ideal map -/

/-- The pulled back ideal `(f')^* J`, the source of the ambient ideal map of **Stacks 08KZ**. -/
abbrev pulledIdeal : SheafOfModules.{u} (structureSheafRing D.X') :=
  (modulePullback D.f').obj D.idealJ

/-- The kernel ideal inclusion `I ⟶ 𝒪_{X'}`. -/
abbrev idealιI : D.idealI ⟶ SheafOfModules.unit (structureSheafRing D.X') :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i))

/-- The kernel ideal inclusion `J ⟶ 𝒪_{S'}`. -/
abbrev idealιJ : D.idealJ ⟶ SheafOfModules.unit (structureSheafRing D.S') :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.t))

/-- The ambient ideal map commutes with restriction. -/
theorem ambientIdealMap_restrict {V W : Opens D.X'.carrier} (i : W ⟶ V)
    (p : D.pulledIdeal.val.obj (op V)) :
    D.X'.presheaf.map i.op (D.ambientIdealMap.val.app (op V) p) =
      D.ambientIdealMap.val.app (op W) (D.pulledIdeal.val.map i.op p) :=
  (ConcreteCategory.congr_hom (D.ambientIdealMap.val.naturality i.op) p).symm

/-- The germs at `x` of the sections of `𝒪_{X'}` lying in the range of the ambient ideal map. -/
def germRange (x : D.X'.carrier) : Set (D.X'.presheaf.stalk x) :=
  {g | ∃ (V : Opens D.X'.carrier) (hx : x ∈ V) (p : D.pulledIdeal.val.obj (op V)),
    D.X'.presheaf.germ V x hx (D.ambientIdealMap.val.app (op V) p) = g}

/-- The germs at `x` of sections in the range of the ambient ideal map form an ideal of the stalk:
the range is a submodule on each open, and restriction to an intersection compares germs. -/
def germIdeal (x : D.X'.carrier) : Ideal (D.X'.presheaf.stalk x) where
  carrier := D.germRange x
  zero_mem' := ⟨⊤, Opens.mem_top x, 0,
    (congrArg (D.X'.presheaf.germ ⊤ x (Opens.mem_top x)) (map_zero _)).trans (map_zero _)⟩
  add_mem' := by
    rintro g₁ g₂ ⟨V₁, h₁, p₁, rfl⟩ ⟨V₂, h₂, p₂, rfl⟩
    have hx : x ∈ V₁ ⊓ V₂ := ⟨h₁, h₂⟩
    let a₁ : D.X'.presheaf.obj (op V₁) := D.ambientIdealMap.val.app (op V₁) p₁
    let a₂ : D.X'.presheaf.obj (op V₂) := D.ambientIdealMap.val.app (op V₂) p₂
    let q₁ : D.pulledIdeal.val.obj (op (V₁ ⊓ V₂)) :=
      D.pulledIdeal.val.map (homOfLE inf_le_left).op p₁
    let q₂ : D.pulledIdeal.val.obj (op (V₁ ⊓ V₂)) :=
      D.pulledIdeal.val.map (homOfLE inf_le_right).op p₂
    let z₁ : D.X'.presheaf.obj (op (V₁ ⊓ V₂)) :=
      D.ambientIdealMap.val.app (op (V₁ ⊓ V₂)) q₁
    let z₂ : D.X'.presheaf.obj (op (V₁ ⊓ V₂)) :=
      D.ambientIdealMap.val.app (op (V₁ ⊓ V₂)) q₂
    have e₁ : z₁ = D.X'.presheaf.map (homOfLE inf_le_left).op a₁ :=
      (D.ambientIdealMap_restrict _ p₁).symm
    have e₂ : z₂ = D.X'.presheaf.map (homOfLE inf_le_right).op a₂ :=
      (D.ambientIdealMap_restrict _ p₂).symm
    refine ⟨V₁ ⊓ V₂, hx, q₁ + q₂, ?_⟩
    rw [map_add]
    change D.X'.presheaf.germ (V₁ ⊓ V₂) x hx (z₁ + z₂) = _
    rw [map_add, e₁, e₂, D.X'.presheaf.germ_res_apply (homOfLE inf_le_left) x hx,
      D.X'.presheaf.germ_res_apply (homOfLE inf_le_right) x hx]
  smul_mem' := by
    rintro c g ⟨V, hV, p, rfl⟩
    obtain ⟨V', hV', b, rfl⟩ := D.X'.presheaf.exists_germ_eq c
    have hx : x ∈ V ⊓ V' := ⟨hV, hV'⟩
    let bW : (structureSheafRing D.X').obj.obj (op (V ⊓ V')) :=
      D.X'.presheaf.map (homOfLE inf_le_right).op b
    let aV : D.X'.presheaf.obj (op V) := D.ambientIdealMap.val.app (op V) p
    let pW : D.pulledIdeal.val.obj (op (V ⊓ V')) :=
      D.pulledIdeal.val.map (homOfLE inf_le_left).op p
    let yP : D.X'.presheaf.obj (op (V ⊓ V')) :=
      D.ambientIdealMap.val.app (op (V ⊓ V')) pW
    have ey : yP = D.X'.presheaf.map (homOfLE inf_le_left).op aV :=
      (D.ambientIdealMap_restrict _ p).symm
    refine ⟨V ⊓ V', hx, bW • pW, ?_⟩
    rw [smul_eq_mul, map_smul]
    change D.X'.presheaf.germ (V ⊓ V') x hx
      (D.X'.presheaf.map (homOfLE inf_le_right).op b * yP) = _
    rw [map_mul, ey, D.X'.presheaf.germ_res_apply (homOfLE inf_le_left) x hx,
      D.X'.presheaf.germ_res_apply (homOfLE inf_le_right) x hx]

/-- The quotient of the stalk of `𝒪_{X'}` at `x` by the germs of the range of the ambient ideal
map. This is the ring of coefficients of the test object. -/
def stalkQuotient (x : D.X'.carrier) : CommRingCat.{u} :=
  CommRingCat.of (D.X'.presheaf.stalk x ⧸ D.germIdeal x)

/-- The quotient map onto `stalkQuotient`. -/
def stalkQuotientMk (x : D.X'.carrier) : D.X'.presheaf.stalk x ⟶ D.stalkQuotient x :=
  CommRingCat.ofHom (Ideal.Quotient.mk (D.germIdeal x))

/-- A germ is killed by the quotient map exactly when it is the germ of a section in the range of
the ambient ideal map. -/
theorem stalkQuotientMk_eq_zero_iff (x : D.X'.carrier) (g : D.X'.presheaf.stalk x) :
    D.stalkQuotientMk x g = 0 ↔ g ∈ D.germRange x := by
  change (Ideal.Quotient.mk (D.germIdeal x)) g = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-! ### Sections of `J` land in the range of the ambient ideal map -/

/-- A section of `J` over `V` is carried by `(f')^♯` into the range of the ambient ideal map over
`(f')^{-1} V`. This is the specification of the ambient ideal map of **Stacks 08KZ**, transposed
across `(f')^* ⊣ (f')_*` and read on sections. -/
theorem exists_ambientIdealMap_eq_comorphism (V : Opens D.S'.carrier)
    (c : D.idealJ.val.obj (op V)) :
    ∃ p : D.pulledIdeal.val.obj (op ((Opens.map D.f'.hom.base).obj V)),
      D.ambientIdealMap.val.app (op ((Opens.map D.f'.hom.base).obj V)) p =
        D.f'.hom.c.app (op V) (D.idealιJ.val.app (op V) c) := by
  refine ⟨((modulePullbackPushforwardAdjunction D.f').unit.app D.idealJ).val.app (op V) c, ?_⟩
  have key := homEquiv_map_comp_pullbackUnitToUnit D.f' D.idealJ D.idealιJ
  rw [Adjunction.homEquiv_unit] at key
  exact congrArg (fun k => k.val.app (op V) c) key

/-! ### The test object and its comorphism -/

/-- The test object at a point `x` of `X'`: the one-point ringed space with coefficients
`𝒪_{X',x}/𝔞_x`, mapping to `X'` by the germ map followed by the quotient map. -/
def testPoint (x : D.X'.carrier) :
    Stacks.AssociatedSheaf.coefficientPoint (D.stalkQuotient x) ⟶ D.X' :=
  Stacks.AssociatedSheaf.fromCoefficientPointOfHom D.X' x (D.stalkQuotientMk x)

/-- A section over an open neighbourhood of `x` is killed by the comorphism of the test object
exactly when its germ at `x` is the germ of a section in the range of the ambient ideal map. -/
theorem testPoint_c_app_eq_zero_iff (x : D.X'.carrier) {U : Opens D.X'.carrier} (hx : x ∈ U)
    (a : D.X'.presheaf.obj (op U)) :
    (D.testPoint x).hom.c.app (op U) a = 0 ↔
      D.X'.presheaf.germ U x hx a ∈ D.germRange x :=
  (Stacks.AssociatedSheaf.fromCoefficientPointOfHom_c_app_eq_zero_iff D.X' x
    (D.stalkQuotientMk x) hx a).trans (D.stalkQuotientMk_eq_zero_iff x _)

/-- The comorphism of `testPoint x` followed by `f'` kills the ideal `J`: a section of `J` is
carried by `(f')^♯` into the range of the ambient ideal map, hence its germ at `x` is killed by
the quotient map. -/
theorem idealιJ_comp_comorphism_testPoint_eq_zero (x : D.X'.carrier) :
    D.idealιJ ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (D.testPoint x ≫ D.f')) = 0 := by
  ext V c
  by_cases hx : x ∈ (Opens.map D.f'.hom.base).obj V.unop
  · obtain ⟨p, hp⟩ := D.exists_ambientIdealMap_eq_comorphism V.unop c
    exact (D.testPoint_c_app_eq_zero_iff x hx (D.f'.hom.c.app V (D.idealιJ.val.app V c))).2
      ⟨(Opens.map D.f'.hom.base).obj V.unop, hx, p,
        congrArg (D.X'.presheaf.germ ((Opens.map D.f'.hom.base).obj V.unop) x hx) hp⟩
  · have hsub : Subsingleton
        ((Stacks.AssociatedSheaf.coefficientPoint (D.stalkQuotient x)).presheaf.obj
          (op ((Opens.map (D.testPoint x ≫ D.f').hom.base).obj V.unop))) :=
      Stacks.AssociatedSheaf.subsingleton_coefficientPoint_presheaf_obj hx
    exact @Subsingleton.elim _ hsub _ _

/-! ### A cartesian square is strict -/

/-- **Stacks Project, Tag 08L2.** A cartesian square of thickenings is strict.

For a point `x` of `X'` the test object `testPoint x` maps to `X'`, and its composite with `f'`
factors through the thickening `t`; the square, being cartesian, therefore lifts it to `X`, and
the lift forces the comorphism of `testPoint x` to kill `I`. So the germ at `x` of a section of
`I` is a germ of a section in the range of the ambient ideal map, and `(f')^* J ⟶ I` is locally
surjective. -/
@[stacks 08L2 "a cartesian square is strict"]
theorem isStrict_of_isPullback (hc : IsPullback D.i D.f D.f' D.t) : D.IsStrict := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective D.idealMap.1 ?_
  constructor
  intro U s x hx
  -- the test object at `x`, and the lift supplied by the cartesian square
  obtain ⟨h, hh⟩ := exists_factorization_of_comp_idealι_eq_zero D.t
    (D.testPoint x ≫ D.f') D.t_isThickening (D.idealιJ_comp_comorphism_testPoint_eq_zero x)
  let l := hc.lift (D.testPoint x) h hh.symm
  have hl : l ≫ D.i = D.testPoint x := hc.lift_fst _ _ _
  -- the comorphism of the test object kills `I`
  have hker : D.i.hom.c.app (op U) (D.idealιI.val.app (op U) s) = 0 :=
    congrArg (fun k : D.idealI ⟶ (modulePushforward D.i).obj
      (SheafOfModules.unit (structureSheafRing D.X)) => k.val.app (op U) s)
      (kernel.condition (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.i)))
  have h1 : (l ≫ D.i).hom.c.app (op U) (D.idealιI.val.app (op U) s) = 0 := by
    change (l.hom.c.app (op ((Opens.map D.i.hom.base).obj U)))
      (D.i.hom.c.app (op U) (D.idealιI.val.app (op U) s)) = 0
    rw [hker, map_zero]
  have h2 := ConcreteCategory.congr_hom (SheafedSpace.congr_hom_app hl.symm (op U))
    (D.idealιI.val.app (op U) s)
  have hzero : (D.testPoint x).hom.c.app (op U) (D.idealιI.val.app (op U) s) = 0 :=
    h2.trans ((ConcreteCategory.comp_apply _ _ _).trans (by rw [h1, map_zero]))
  -- hence the germ of `s` at `x` is the germ of a section in the range of the ambient ideal map
  obtain ⟨V, hxV, p, hp⟩ := (D.testPoint_c_app_eq_zero_iff x hx
    (D.idealιI.val.app (op U) s)).1 hzero
  obtain ⟨W, hxW, iV, iU, hW⟩ := D.X'.presheaf.germ_eq x hxV hx _ _ hp
  refine ⟨W, iU, ⟨D.pulledIdeal.val.map iV.op p, ?_⟩, hxW⟩
  -- the two sections of `I` over `W` agree, because they agree inside `𝒪_{X'}`
  have hinj : Function.Injective (D.idealιI.val.app (op W)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((SheafOfModules.evaluation (R := structureSheafRing D.X') (op W)).map D.idealιI)
    infer_instance
  apply hinj
  have hspec : (D.idealMap.1 ≫ D.idealιI).val.app (op W) (D.pulledIdeal.val.map iV.op p) =
      D.ambientIdealMap.val.app (op W) (D.pulledIdeal.val.map iV.op p) :=
    ConcreteCategory.congr_hom (congrArg (fun k : D.pulledIdeal ⟶
      SheafOfModules.unit (structureSheafRing D.X') => k.val.app (op W)) D.idealMap.2) _
  refine hspec.trans ?_
  rw [← D.ambientIdealMap_restrict iV p, hW]
  exact (ConcreteCategory.congr_hom (D.idealιI.val.naturality iU.op) s).symm

/-- **Stacks Project, Tag 08L2.** A morphism of thickenings of ringed spaces is strict if and
only if its square is cartesian in the category of ringed spaces. The forward implication is
`isPullback_of_isStrict`; the converse is `isStrict_of_isPullback`. -/
@[stacks 08L2 "strict iff cartesian"]
theorem isStrict_iff_isPullback : D.IsStrict ↔ IsPullback D.i D.f D.f' D.t :=
  ⟨D.isPullback_of_isStrict, D.isStrict_of_isPullback⟩

end AlgebraicGeometry.RingedSpaceThickening.MorphismOfThickenings

end
