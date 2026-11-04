module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Basic

/-!
# Sections over an object of the small étale site of an affine scheme, as `A`-modules

For an object `V` of the small étale site of `X = Spec A`, the sections `H(V)` of an
`𝒪_étale`-module are a module over `𝒪(V)`, hence an `A`-module along the ring map
`ρ_V : A ⟶ 𝒪(⊤) ⟶ 𝒪(V)`. This file identifies that `A`-module with the sections read through the
slice adjunction (`AlgebraicGeometry.AffineEtaleDuality.secV`), and restates the universal property
of `ε^*T` on the slice over `V` with this target.

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.ρtop` and `AlgebraicGeometry.AffineEtaleDuality.ρV`: the
  ring maps `A ⟶ 𝒪(⊤)` and `A ⟶ 𝒪(V)`.
* `AlgebraicGeometry.AffineEtaleDuality.secA`: sections over `V` as an `A`-module.
* `AlgebraicGeometry.AffineEtaleDuality.secVIso`: the natural isomorphism `secV V ≅ secA V`.
* `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquivA`: morphisms `(ε^*T M)|_V ⟶ H|_V` are
  `A`-linear maps `M ⟶ H(V)`.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquivA_apply`: the correspondence evaluates at
  `V` on the canonical sections.
* `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquivA_comp_left` and
  `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquivA_comp_right`: its naturality in both
  variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The ring map `A ⟶ 𝒪(⊤)` along which `A` acts on global sections. -/
def ρtop : A →+* ((O A B hX).obj.obj (op (top A B hX)) : RingCat) :=
  ((SmallEtale.structureMap B (Spec A) hX).hom.app (op ⊤)).hom.comp (Scheme.ΓSpecIso A).inv.hom

/-- The ring map `A ⟶ 𝒪(V)`: the ring map to `𝒪(⊤)` followed by restriction to `V`. -/
def ρV (V : Site A B hX) : A →+* ((O A B hX).obj.obj (op V) : RingCat) :=
  ((O A B hX).obj.map (toTop A B hX V).op).hom.comp (ρtop A B hX)

/-- The sections over `V` of an `𝒪_étale`-module, as an `A`-module along `ρ_V`. -/
abbrev secA (V : Site A B hX) : Mod A B hX ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation (O A B hX) (op V) ⋙ ModuleCat.restrictScalars (ρV A B hX V)

/-- The functor `secA V` is additive. -/
instance secA_additive (V : Site A B hX) : (secA A B hX V).Additive where
  map_add := by intros; rfl

/-- On `secA V`, the element `a : A` acts on a section by `ρV a`. -/
lemma secA_smul (V : Site A B hX) (H : Mod A B hX) (a : A) (x : (secA A B hX V).obj H) :
    a • x = (show H.val.obj (op V) from (ρV A B hX V a • (show H.val.obj (op V) from x))) :=
  rfl

/-- On global sections, the element `a : A` acts on a section by `ρtop a`. -/
lemma gammaTop_smul (H : Mod A B hX) (a : A) (x : (gammaTop A B hX).obj H) :
    a • x = (show H.val.obj (op (top A B hX)) from
      (ρtop A B hX a • (show H.val.obj (op (top A B hX)) from x))) :=
  rfl

/-- On `secV V`, the element `a : A` acts on a section over `V ⨯ ⊤` by the restriction of
`ρtop a` along the projection `V ⨯ ⊤ ⟶ ⊤`. -/
lemma secV_smul (V : Site A B hX) (H : Mod A B hX) (a : A) (x : (secV A B hX V).obj H) :
    a • x = (show H.val.obj (op (V ⨯ top A B hX)) from
      (((O A B hX).obj.map (prod.snd : V ⨯ top A B hX ⟶ top A B hX).op).hom (ρtop A B hX a) •
        (show H.val.obj (op (V ⨯ top A B hX)) from x))) :=
  rfl

/-- The sections of `secV V` are the `A`-module of sections over `V`. -/
def secVLinearEquiv (V : Site A B hX) (H : Mod A B hX) :
    ((secV A B hX V).obj H : Type u) ≃ₗ[A] ((secA A B hX V).obj H : Type u) where
  __ := secVAddEquiv A B hX V H
  map_smul' a x := by
    change H.val.map (toProdTop A B hX V).op (a • x) = ρV A B hX V a • H.val.map
      (toProdTop A B hX V).op x
    rw [secV_smul, PresheafOfModules.map_smul]
    congr 1
    change ((O A B hX).obj.map (prod.snd : V ⨯ top A B hX ⟶ top A B hX).op ≫
      (O A B hX).obj.map (toProdTop A B hX V).op).hom (ρtop A B hX a) = _
    rw [← CategoryTheory.Functor.map_comp, ← op_comp,
      toTop_eq A B hX (toProdTop A B hX V ≫ prod.snd)]
    rfl

/-- **`secV V ≅ secA V`**, naturally in the module. -/
def secVIso (V : Site A B hX) : secV A B hX V ≅ secA A B hX V :=
  NatIso.ofComponents (fun H => (secVLinearEquiv A B hX V H).toModuleIso) fun {H H'} f => by
    ext x
    exact (PresheafOfModules.naturality_apply f.val (toProdTop A B hX V).op x).symm

/-- The isomorphism `secVIso V` acts on sections as `secVAddEquiv`. -/
lemma secVIso_hom_app_apply (V : Site A B hX) (H : Mod A B hX) (x : (secV A B hX V).obj H) :
    ((secVIso A B hX V).hom.app H) x = secVAddEquiv A B hX V H x := rfl

/-- Restriction of global sections to `V`, as an `A`-linear map. -/
def resTopApp (V : Site A B hX) (H : Mod A B hX) :
    (gammaTop A B hX).obj H ⟶ (secA A B hX V).obj H :=
  ModuleCat.ofHom (X := (gammaTop A B hX).obj H) (Y := (secA A B hX V).obj H)
    { toFun := fun x => H.val.map (toTop A B hX V).op
        (show H.val.obj (op (top A B hX)) from x)
      map_add' := fun x y => map_add (H.val.map (toTop A B hX V).op).hom
        (show H.val.obj (op (top A B hX)) from x) y
      map_smul' := fun a x => by
        change H.val.map (toTop A B hX V).op
            (ρtop A B hX a • (show H.val.obj (op (top A B hX)) from x)) =
          ρV A B hX V a • H.val.map (toTop A B hX V).op (show H.val.obj (op (top A B hX)) from x)
        rw [PresheafOfModules.map_smul]
        rfl }

/-- Restriction of global sections to `V`, as a natural transformation `Γ ⟶ secA V`. -/
def resTop (V : Site A B hX) : gammaTop A B hX ⟶ secA A B hX V where
  app := resTopApp A B hX V
  naturality {H H'} f := by
    ext x
    exact (PresheafOfModules.naturality_apply f.val (toTop A B hX V).op
      (show H.val.obj (op (top A B hX)) from x)).symm

/-- The canonical section `unitSectionAt`, as an `A`-linear map. -/
def unitSectionAtLinear (M : ModuleCat.{u} A) (V : Site A B hX) :
    M ⟶ (secA A B hX V).obj ((epsT A B hX).obj M) :=
  (epsTAdj A B hX).unit.app M ≫ (resTop A B hX V).app _

/-- The map `unitSectionAtLinear` sends `m` to the canonical section `unitSectionAt M V m`. -/
lemma unitSectionAtLinear_apply (M : ModuleCat.{u} A) (V : Site A B hX) (m : M) :
    (show ((epsT A B hX).obj M).val.obj (op V) from unitSectionAtLinear A B hX M V m) =
      unitSectionAt A B hX M V m := rfl

/-- The canonical sections are natural in the module. -/
lemma unitSectionAt_naturality {M M' : ModuleCat.{u} A} (f : M ⟶ M') (V : Site A B hX) (m : M) :
    ((epsT A B hX).map f).val.app (op V) (unitSectionAt A B hX M V m) =
      unitSectionAt A B hX M' V (f m) := by
  have h1 := PresheafOfModules.naturality_apply ((epsT A B hX).map f).val (toTop A B hX V).op
    (((epsTAdj A B hX).unit.app M).hom m)
  refine h1.trans ?_
  exact congrArg (((epsT A B hX).obj M').val.map (toTop A B hX V).op)
    (congrArg (fun h => h.hom m) ((epsTAdj A B hX).unit.naturality f).symm)

/-! ### The universal property on the slice, with `A`-module target -/

/-- **Morphisms out of the restriction of `ε^*T M` to `V` are `A`-linear maps out of `M` into the
sections over `V`.** -/
def sliceHomEquivA (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX) :
    (((epsT A B hX).obj M).over V ⟶ H.over V) ≃ (M ⟶ (secA A B hX V).obj H) :=
  (sliceHomEquiv A B hX M H V).trans ((secVIso A B hX V).app H).homToEquiv

/-- The correspondence `sliceHomEquivA` evaluates a morphism at `V` on the canonical sections. -/
lemma sliceHomEquivA_apply (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX)
    (φ : ((epsT A B hX).obj M).over V ⟶ H.over V) (m : M) :
    (show H.val.obj (op V) from sliceHomEquivA A B hX M H V φ m) =
      φ.val.app (op (Over.mk (𝟙 V))) (unitSectionAt A B hX M V m) :=
  sliceHomEquiv_apply A B hX M H V φ m

/-- `sliceHomEquivA` is natural in the target. -/
lemma sliceHomEquivA_comp_right (M : ModuleCat.{u} A) {H H' : Mod A B hX} (V : Site A B hX)
    (φ : ((epsT A B hX).obj M).over V ⟶ H.over V) (g : H ⟶ H') :
    sliceHomEquivA A B hX M H' V (φ ≫ (SheafOfModules.overFunctor (O A B hX) V).map g) =
      sliceHomEquivA A B hX M H V φ ≫ (secA A B hX V).map g := by
  ext m
  refine (sliceHomEquivA_apply A B hX M H' V _ m).trans ?_
  exact (congrArg (g.val.app (op V)) (sliceHomEquivA_apply A B hX M H V φ m)).symm

/-- `sliceHomEquivA` is natural in the source. -/
lemma sliceHomEquivA_comp_left {M M' : ModuleCat.{u} A} (H : Mod A B hX) (V : Site A B hX)
    (f : M ⟶ M') (φ : ((epsT A B hX).obj M').over V ⟶ H.over V) :
    sliceHomEquivA A B hX M H V
        ((SheafOfModules.overFunctor (O A B hX) V).map ((epsT A B hX).map f) ≫ φ) =
      f ≫ sliceHomEquivA A B hX M' H V φ := by
  ext m
  refine (sliceHomEquivA_apply A B hX M H V _ m).trans ?_
  refine Eq.trans ?_ (sliceHomEquivA_apply A B hX M' H V φ (f m)).symm
  exact congrArg (φ.val.app (op (Over.mk (𝟙 V)))) (unitSectionAt_naturality A B hX f V m)

end AlgebraicGeometry.AffineEtaleDuality

end
