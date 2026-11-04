module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic

/-!
# The forgetful functor of the big crystalline category preserves limits

In a global crystalline situation, a scheme `U` over `X` becomes an object `(U, U, ∅)` of
`CRIS(X/S)`: thicken `U` by itself, and give the ambient scheme the zero divided power ideal.  A
morphism out of `(U, U, ∅)` is determined by its map on thickened schemes, because the immersion
of `(U, U, ∅)` is the identity, and any map into the ambient scheme of another object is
automatically a divided power morphism, because the source divided power ideal is zero.  This
makes `U ↦ (U, U, ∅)` a left adjoint of the forgetful functor `CRIS(X/S) ⥤ Sch/X`, which is
[Stacks, Tag 07I8], and therefore the forgetful functor preserves all limits that exist — the
second assertion of [Stacks, Tag 07I9].

## Main definitions

* `Crystalline.GlobalCrystallineSituation.trivialThickening` — a scheme over `X`, thickened by
  itself, with zero divided power ideal.
* `Crystalline.GlobalCrystallineSituation.free` — the functor `Sch/X ⥤ CRIS(X/S)` of
  [Stacks, Tag 07I8].
* `Crystalline.GlobalCrystallineSituation.ambientDividedPowerScheme` — the functor
  `CRIS(X/S) ⥤ DividedPowerScheme` keeping only the ambient divided power scheme.

## Main results

* `Crystalline.GlobalCrystallineSituation.freeForgetAdjunction` — `free S ⊣ forget S`.
* `Crystalline.GlobalCrystallineSituation.forget_preservesLimits` — the forgetful functor
  `CRIS(X/S) ⥤ Sch/X` preserves every limit that exists.  This is the second assertion of
  [Stacks, Tag 07I9]; the existence of nonempty finite limits in `CRIS(X/S)` is *not* proved here.
* `Crystalline.GlobalCrystallineSituation.isLimitOfComponents` — a cone of `CRIS(X/S)` over a
  nonempty diagram is a limit cone as soon as its cone of ambient divided power schemes and its
  cone of thickened schemes over `X` are limit cones and the ambient projections are jointly
  monic on underlying schemes.  This reduces the first assertion of [Stacks, Tag 07I9] to the
  existence of finite nonempty limits of divided power schemes, [Stacks, Tag 07ME].

## Implementation notes

The adjunction is built from its hom-set bijection rather than from a unit and a counit, because
the bijection is the identity on the map of thickened schemes in both directions: forward, forget
the divided power map; backward, recover it as `h ≫ immersion`.  The only mathematical input is
that the immersion of a divided power thickening kills the divided power ideal of its ambient
scheme (`Crystalline.SchemeThickening.immersion_app_eq_zero_of_mem`), which is what makes the
recovered map a divided power morphism, and the same statement for the closed fibre
`S₀ = V(I) ⊆ S`, which is what makes `(U, U, ∅) ⟶ S` one.

Preservation of limits is `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`.  Note that
this says nothing about which limits exist: `CRIS(X/S)` has no terminal object in general, and for
a shape it does have limits of, this identifies them with the limits of the underlying schemes
over `X`.

Which limits exist is a question about the ambient divided power schemes: an object of
`CRIS(X/S)` is recovered from its ambient scheme `T` together with the map `T₀ ⟶ X` on the closed
fibre, so a cone whose ambient component is a limit cone of divided power schemes and whose
component of thickened schemes is a limit cone over `X` is a limit cone.  The one point that is
not formal is the commuting square of thickenings for the lift, and it needs the ambient
projections to be jointly monic on underlying schemes, which for a fibre product of divided power
schemes holds because its underlying scheme is a closed subscheme of the fibre product of the
underlying schemes.

## References

* [Stacks Project, Tag 07I8](https://stacks.math.columbia.edu/tag/07I8)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe v₁ u₁ u

namespace Crystalline

/-- A section killed by a morphism of schemes is killed by any composite through it. -/
theorem comp_app_eq_zero {X Y Z : Scheme.{u}} (g : X ⟶ Y) (i : Y ⟶ Z) (V : Z.Opens)
    (s : Γ(Z, V)) (h : (i.app V).hom s = 0) : ((g ≫ i).app V).hom s = 0 := by
  have hcomp : ((g ≫ i).app V).hom s = (g.app (i ⁻¹ᵁ V)).hom ((i.app V).hom s) := rfl
  rw [hcomp, h]
  exact map_zero _

/-- **A morphism into the ambient scheme of a divided power scheme is a divided power morphism out
of the trivial divided power structure as soon as it kills the divided power ideal.**  The source
divided power ideal is zero, so `DividedPowers.IsDPMorphism.of_eq_bot` applies. -/
theorem isDPMorphism_trivialDividedPowerScheme {X : Scheme.{u}} {Y : DividedPowerScheme.{u}}
    (g : X ⟶ Y.scheme)
    (hg : ∀ (V : Y.scheme.Opens) (s : Γ(Y.scheme, V)), s ∈ Y.ideal.obj (op V) →
      (g.app V).hom s = 0)
    (V : Y.scheme.Opens) :
    DividedPowers.IsDPMorphism (Y.dividedPowers.dividedPowers (op V))
      ((trivialDividedPowerScheme X).dividedPowers.dividedPowers (op (g ⁻¹ᵁ V)))
      (g.app V).hom :=
  DividedPowers.IsDPMorphism.of_eq_bot _ _ _ (SheafOfModules.Submodule.bot_obj _ _)
    (Ideal.map_le_iff_le_comap.mpr fun s hs ↦
      show (g.app V).hom s ∈ (trivialDividedPowerScheme X).ideal.obj (op (g ⁻¹ᵁ V)) from
        (SheafOfModules.Submodule.bot_obj _ (op (g ⁻¹ᵁ V))).ge
          ((Submodule.mem_bot _).mpr (hg V s hs)))

/-- The kernel ideal sheaf of the identity is zero, in the spelling the divided power ideal of
`Crystalline.trivialDividedPowerScheme` presents it. -/
theorem bot_obj_eq_ker_id (U : Scheme.{u}) (V : U.affineOpens) :
    (trivialDividedPowerScheme U).ideal.obj (op (V : U.Opens)) =
      (Scheme.Hom.ker (𝟙 U)).ideal V := by
  have h2 : (Scheme.Hom.ker (𝟙 U)).ideal V = ⊥ := by
    rw [Scheme.Hom.ker_eq_bot_of_isIso]; rfl
  refine Eq.trans ?_ h2.symm
  exact SheafOfModules.Submodule.bot_obj _ (op (V : U.Opens))

/-- The identity of a scheme is a thickening. -/
theorem isThickening_id (U : Scheme.{u}) : IsThickening (𝟙 U) :=
  ⟨inferInstance, Function.surjective_id⟩

namespace GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- The structure morphism of the trivial thickening of a scheme over `X` kills the divided power
ideal of `S`, because it factors through the closed fibre `S₀ = V(I)`. -/
theorem sourceToBase_app_eq_zero {U : Scheme.{u}} (g : U ⟶ S.X) (W : S.S.scheme.Opens)
    (s : Γ(S.S.scheme, W)) (hs : s ∈ S.S.ideal.obj (op W)) :
    ((g ≫ sourceToBase S).app W).hom s = 0 :=
  comp_app_eq_zero g (sourceToBase S) W s
    (comp_app_eq_zero S.toClosedFiber (DividedPowerScheme.closedFiberι S.S) W s
      ((DividedPowerScheme.closedFiberPresentation S.S).app_eq_zero_of_mem W s hs))

/-- The structure morphism `U ⟶ S` of the trivial thickening of a scheme over `X`, as a divided
power morphism. -/
def trivialToBase {U : Scheme.{u}} (g : U ⟶ S.X) : trivialDividedPowerScheme U ⟶ S.S where
  hom := g ≫ sourceToBase S
  compatible :=
    isDPMorphism_trivialDividedPowerScheme (X := U) (Y := S.S) (g ≫ sourceToBase S)
      (sourceToBase_app_eq_zero S g)

/-- **The trivial divided power thickening of a scheme by itself, over `X`.**  This is the object
`(U, U, ∅)` of [Stacks, Tag 07I8]: the identity of `U` is a thickening, and the zero divided power
ideal of `Crystalline.trivialDividedPowerScheme` is its defining ideal. -/
def trivialThickening {U : Scheme.{u}} (g : U ⟶ S.X) : Thickening S where
  thickening :=
    { source := U
      target := trivialDividedPowerScheme U
      immersion := 𝟙 U
      isThickening := isThickening_id U
      ideal_eq_ker := bot_obj_eq_ker_id U }
  toBase := trivialToBase S g
  toX := g
  over_base := Category.id_comp _

/-- The underlying morphism of schemes of `trivialToBase S g` is `g` followed by the structure
morphism `X ⟶ S`. -/
@[simp]
theorem trivialToBase_hom {U : Scheme.{u}} (g : U ⟶ S.X) :
    (trivialToBase S g).hom = g ≫ sourceToBase S := rfl

/-- Naturality of the structure morphism of a trivial thickening. -/
theorem comp_trivialToBase_hom {U U' : Scheme.{u}} (p : U ⟶ U') (g : U' ⟶ S.X) (g' : U ⟶ S.X)
    (hp : p ≫ g = g') : p ≫ (g ≫ sourceToBase S) = g' ≫ sourceToBase S := by
  rw [← Category.assoc, hp]

/-- The structure morphism of an object of `CRIS(X/S)`, precomposed with a map into its thickened
scheme, is the structure morphism of the trivial thickening of the source. -/
theorem comp_immersion_comp_toBase {U : Scheme.{u}} (A : Thickening S)
    (q : U ⟶ A.thickening.source) (g : U ⟶ S.X) (hw : q ≫ A.toX = g) :
    (q ≫ A.thickening.immersion) ≫ A.toBase.hom = g ≫ sourceToBase S := by
  rw [Category.assoc, A.over_base, ← Category.assoc, hw]

/-- A morphism between trivial divided power schemes is automatically a divided power morphism,
both ideals being zero. -/
theorem isDPMorphism_trivial_trivial {U U' : Scheme.{u}} (h : U ⟶ U') :
    ∀ V : U'.Opens,
      DividedPowers.IsDPMorphism
        ((trivialDividedPowerScheme U').dividedPowers.dividedPowers (op V))
        ((trivialDividedPowerScheme U).dividedPowers.dividedPowers (op (h ⁻¹ᵁ V)))
        (h.app V).hom :=
  isDPMorphism_trivialDividedPowerScheme (X := U) (Y := trivialDividedPowerScheme U') h
    fun W s hs ↦ by
      rw [(Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj _ (op W)).le hs)]
      exact map_zero _

/-- **Stacks Project, Tag 07I8.** A scheme over `X`, viewed as the divided power thickening
`(U, U, ∅)` of `X` relative to `S`.  This is a one-sided inverse of the forgetful functor, and its
left adjoint. -/
@[stacks 07I8]
def free : Over S.X ⥤ Thickening S where
  obj U :=
    { thickening :=
        { source := U.left
          target := trivialDividedPowerScheme U.left
          immersion := 𝟙 U.left
          isThickening := isThickening_id U.left
          ideal_eq_ker := bot_obj_eq_ker_id U.left }
      toBase := trivialToBase S U.hom
      toX := U.hom
      over_base := Category.id_comp _ }
  map {U U'} f :=
    { sourceHom := f.left
      targetHom :=
        { hom := f.left
          compatible := isDPMorphism_trivial_trivial f.left }
      immersion_naturality := (Category.id_comp _).trans (Category.comp_id _).symm
      base_naturality :=
        DividedPowerScheme.Hom.ext (comp_trivialToBase_hom S f.left U'.hom U.hom f.w)
      toX_naturality := f.w }
  map_id := fun _ ↦ Thickening.Hom.ext rfl (DividedPowerScheme.Hom.ext rfl)
  map_comp := fun _ _ ↦ Thickening.Hom.ext rfl (DividedPowerScheme.Hom.ext rfl)

/-- **Stacks Project, Tag 07I8.** The trivial thickening is left adjoint to the forgetful functor:
a morphism `(U, U, ∅) ⟶ (U', T', δ')` is exactly a morphism `U ⟶ U'` over `X`.  Its divided power
map on ambient schemes is forced to be `U ⟶ U' ↪ T'`, which is a divided power morphism because
the immersion `U' ↪ T'` kills the divided power ideal of `T'`. -/
def freeForgetAdjunction : free S ⊣ forget S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun U A ↦
        { toFun := fun f ↦ by exact Over.homMk f.sourceHom f.toX_naturality
          invFun := fun h ↦ by exact
            { sourceHom := h.left
              targetHom :=
                { hom := h.left ≫ A.thickening.immersion
                  compatible :=
                    isDPMorphism_trivialDividedPowerScheme (X := U.left)
                      (Y := A.thickening.target) (h.left ≫ A.thickening.immersion)
                      fun W s hs ↦ comp_app_eq_zero h.left A.thickening.immersion W s
                        (A.thickening.immersion_app_eq_zero_of_mem W s hs) }
              immersion_naturality := Category.id_comp _
              base_naturality :=
                DividedPowerScheme.Hom.ext (comp_immersion_comp_toBase S A h.left U.hom h.w)
              toX_naturality := h.w }
          left_inv := fun f ↦ Thickening.Hom.ext rfl (DividedPowerScheme.Hom.ext
            ((Category.id_comp _).symm.trans f.immersion_naturality).symm)
          right_inv := fun h ↦ Over.OverMorphism.ext rfl }
      homEquiv_naturality_left_symm := fun f g ↦
        Thickening.Hom.ext rfl (DividedPowerScheme.Hom.ext (Category.assoc _ _ _))
      homEquiv_naturality_right := fun f g ↦ Over.OverMorphism.ext rfl }

/-- **Stacks Project, Tag 07I9, second assertion.** The forgetful functor `CRIS(X/S) ⥤ Sch/X`
preserves every limit that exists, being a right adjoint. -/
@[stacks 07I9 "the functor (07I7) commutes with limits"]
instance forget_preservesLimits : PreservesLimits (forget S) :=
  (freeForgetAdjunction S).rightAdjoint_preservesLimits

/-- **The ambient divided power scheme of an object of `CRIS(X/S)`.**  Forgetting the thickened
scheme and the map to `X` leaves the divided power scheme `T` and the divided power maps between
such, so `(U, T, δ) ↦ T` is a functor `CRIS(X/S) ⥤ DividedPowerScheme`. -/
def ambientDividedPowerScheme : Thickening S ⥤ DividedPowerScheme.{u} where
  obj A := A.thickening.target
  map f := f.targetHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The ambient divided power scheme of a thickening `(U, T, δ)` is `T`. -/
@[simp]
theorem ambientDividedPowerScheme_obj (A : Thickening S) :
    (ambientDividedPowerScheme S).obj A = A.thickening.target := rfl

/-- The functor `ambientDividedPowerScheme S` sends a morphism of thickenings to its divided
power morphism of ambient schemes. -/
@[simp]
theorem ambientDividedPowerScheme_map {A B : Thickening S} (f : A ⟶ B) :
    (ambientDividedPowerScheme S).map f = f.targetHom := rfl

section LimitCriterion

variable {J : Type u₁} [Category.{v₁} J] [Nonempty J] {F : J ⥤ Thickening S}

/-- **A cone of `CRIS(X/S)` over a nonempty diagram is a limit cone as soon as its ambient
divided power schemes and its thickened schemes over `X` are, provided the ambient projections
are jointly monic on underlying schemes.**  The lift is assembled from the lifts of the two
component cones; joint monicity of the ambient projections is what forces the two lifts to form a
commuting square of thickenings, and nonemptiness of the diagram is what identifies the structure
morphism of the apex over the divided power base.

For a fibre product of divided power schemes the ambient apex is a closed subscheme of the fibre
product of the underlying schemes, so the ambient projections are indeed jointly monic. -/
def isLimitOfComponents (c : Cone F)
    (hamb : IsLimit ((ambientDividedPowerScheme S).mapCone c))
    (hmono : ∀ {W : Scheme.{u}} (a b : W ⟶ c.pt.thickening.target.scheme),
      (∀ j, a ≫ (c.π.app j).targetHom.hom = b ≫ (c.π.app j).targetHom.hom) → a = b)
    (hsrc : IsLimit ((forget S).mapCone c)) : IsLimit c where
  lift s :=
    { sourceHom := (hsrc.lift ((forget S).mapCone s)).left
      targetHom := hamb.lift ((ambientDividedPowerScheme S).mapCone s)
      immersion_naturality := by
        set lt : s.pt.thickening.target ⟶ c.pt.thickening.target :=
          hamb.lift ((ambientDividedPowerScheme S).mapCone s) with hlt
        set ls : s.pt.thickening.source ⟶ c.pt.thickening.source :=
          (hsrc.lift ((forget S).mapCone s)).left with hls
        refine hmono _ _ fun j ↦ ?_
        have hfa : lt ≫ (c.π.app j).targetHom = (s.π.app j).targetHom := by
          rw [hlt]; exact hamb.fac ((ambientDividedPowerScheme S).mapCone s) j
        have hfs : ls ≫ (c.π.app j).sourceHom = (s.π.app j).sourceHom := by
          rw [hls]
          simpa [Functor.mapCone_π_app] using
            congrArg (fun h ↦ h.left) (hsrc.fac ((forget S).mapCone s) j)
        have hci : c.pt.thickening.immersion ≫ (c.π.app j).targetHom.hom =
            (c.π.app j).sourceHom ≫ (F.obj j).thickening.immersion :=
          (c.π.app j).immersion_naturality
        have hsi : s.pt.thickening.immersion ≫ (s.π.app j).targetHom.hom =
            (s.π.app j).sourceHom ≫ (F.obj j).thickening.immersion :=
          (s.π.app j).immersion_naturality
        rw [Category.assoc, ← DividedPowerScheme.Hom.comp_hom, hfa, hsi, Category.assoc, hci,
          ← Category.assoc, hfs]
      base_naturality := by
        obtain ⟨j⟩ := ‹Nonempty J›
        set lt : s.pt.thickening.target ⟶ c.pt.thickening.target :=
          hamb.lift ((ambientDividedPowerScheme S).mapCone s) with hlt
        have hfa : lt ≫ (c.π.app j).targetHom = (s.π.app j).targetHom := by
          rw [hlt]; exact hamb.fac ((ambientDividedPowerScheme S).mapCone s) j
        have hcb : (c.π.app j).targetHom ≫ (F.obj j).toBase = c.pt.toBase :=
          (c.π.app j).base_naturality
        have hsb : (s.π.app j).targetHom ≫ (F.obj j).toBase = s.pt.toBase :=
          (s.π.app j).base_naturality
        rw [← hcb, ← Category.assoc, hfa, hsb]
      toX_naturality := Over.w (hsrc.lift ((forget S).mapCone s)) }
  fac s j := by
    refine Thickening.Hom.ext ?_ ?_
    · simpa [Functor.mapCone_π_app] using
        congrArg (fun h ↦ h.left) (hsrc.fac ((forget S).mapCone s) j)
    · simpa [Functor.mapCone_π_app] using hamb.fac ((ambientDividedPowerScheme S).mapCone s) j
  uniq s m hm := by
    have h2 : (forget S).map m = hsrc.lift ((forget S).mapCone s) :=
      hsrc.uniq ((forget S).mapCone s) ((forget S).map m) fun j ↦ by
        simp only [Functor.mapCone_π_app, ← CategoryTheory.Functor.map_comp]
        exact congrArg (fun k ↦ (forget S).map k) (hm j)
    have h1 : (ambientDividedPowerScheme S).map m =
        hamb.lift ((ambientDividedPowerScheme S).mapCone s) :=
      hamb.uniq ((ambientDividedPowerScheme S).mapCone s)
        ((ambientDividedPowerScheme S).map m) fun j ↦ by
        simp only [Functor.mapCone_π_app, ← CategoryTheory.Functor.map_comp]
        exact congrArg (fun k ↦ (ambientDividedPowerScheme S).map k) (hm j)
    exact Thickening.Hom.ext (congrArg (fun h ↦ h.left) h2) h1

end LimitCriterion

end GlobalCrystallineSituation

end Crystalline

end
