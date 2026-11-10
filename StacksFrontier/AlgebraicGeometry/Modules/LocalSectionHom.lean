module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion

/-!
# Local sections of a module as morphisms out of the structure sheaf

Let `X` be a scheme, `V` an open of `X` and `F` an `𝒪_X`-module. A section `s ∈ Γ(F, V)`
determines a morphism `𝒪_V ⟶ F|_V` of modules on the open subscheme `V`, namely `r ↦ r • s`,
and every such morphism arises from exactly one section: the sections of `F` over `V` are the
morphisms `𝒪_V ⟶ F|_V`. The dictionary is additive, carries `1 ∈ Γ(X, V)` to the identity of
`𝒪_V`, is natural in `F`, and turns precomposition with the restriction of an endomorphism `c`
of `𝒪_X` into multiplication by the scalar `c(1) ∈ Γ(X, V)`.

The same dictionary for a finite family: a family `s : ι → Γ(F, V)` is a morphism
`(𝒪_V)^ι ⟶ F|_V`, a morphism out of `(𝒪_V)^ι` is determined by its `ι` coordinates, and
precomposing with the restriction of a morphism `c : 𝒪_X ⟶ (𝒪_X)^ι` produces the single
section `∑ i, c_i • s i`.

## Main definitions

* `Stacks.AlgebraicGeometry.LocalSection.localSectionHom`: a section of `F` over `V`, read as a
  morphism `𝒪_V ⟶ F|_V`.
* `Stacks.AlgebraicGeometry.LocalSection.unitHomScalar`: the scalar `c(1) ∈ Γ(X, V)` attached to
  an endomorphism `c` of the structure sheaf.
* `Stacks.AlgebraicGeometry.LocalSection.localFreeHom`: a finite family of sections of `F` over
  `V`, read as a morphism `(𝒪_V)^ι ⟶ F|_V`.

## Main results

* `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_injective` and
  `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_surjective`: **the sections of `F` over
  `V` are exactly the morphisms `𝒪_V ⟶ F|_V`.**
* `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_zero`,
  `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_add`,
  `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_one`,
  `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_natural` and
  `Stacks.AlgebraicGeometry.LocalSection.localSectionHom_precomp`: the dictionary is additive,
  unital, natural in `F`, and compatible with precomposition by an endomorphism of `𝒪_X`.
* `Stacks.AlgebraicGeometry.LocalSection.localFreeHom_ι`,
  `Stacks.AlgebraicGeometry.LocalSection.localFreeHom_precomp` and
  `Stacks.AlgebraicGeometry.LocalSection.localFreeHom_ext`: the coordinates of the free version,
  the linear combination it produces, and the fact that a morphism out of `(𝒪_V)^ι` is
  determined by its coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.AlgebraicGeometry.LocalSection

variable {X : Scheme.{u}}

/-- A section `s` of `F` over the open `V`, read as a morphism `𝒪_V ⟶ F|_V` of modules on the
open subscheme `V`: over an open `W` of `V` it sends a function `r` to `r • s|_W`. -/
def localSectionHom (V : X.Opens) (F : X.Modules) (s : Γ(F, V)) :
    Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) V.ι ⟶ F.restrict V.ι where
  val := PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        { toFun := fun (r : Γ(X, V.ι ''ᵁ W.unop)) =>
            r • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s
          map_zero' := by
            change (0 : Γ(X, V.ι ''ᵁ W.unop)) • (_ : Γ(F, V.ι ''ᵁ W.unop)) = 0
            exact zero_smul _ _
          map_add' := fun r t => by
            change Γ(X, V.ι ''ᵁ W.unop) at r t
            change (r + t) • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s =
              r • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s +
                t • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s
            exact add_smul r t _ }
      naturality := by
        intro W Z f
        ext r
        change Γ(X, V.ι ''ᵁ W.unop) at r
        change @SMul.smul Γ(X, V.ι ''ᵁ Z.unop) Γ(F, V.ι ''ᵁ Z.unop) _
            (X.presheaf.map (V.ι.opensFunctor.op.map f) r)
            (F.presheaf.map (homOfLE (V.ι_image_le Z.unop)).op s) =
          F.presheaf.map (V.ι.opensFunctor.op.map f)
            (r • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)
        have hm := F.val.map_smul (V.ι.opensFunctor.op.map f) r
          (F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)
        change F.presheaf.map (V.ι.opensFunctor.op.map f)
            (r • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s) = _ at hm
        rw [hm]
        congr 1
        change F.presheaf.map (homOfLE (V.ι_image_le Z.unop)).op s =
          F.presheaf.map (V.ι.opensFunctor.op.map f)
            (F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)
        exact ConcreteCategory.congr_hom (F.presheaf.map_comp
          (homOfLE (V.ι_image_le W.unop)).op (V.ι.opensFunctor.op.map f)) s }
    (fun W r => by
      intro t
      change Γ(X, V.ι ''ᵁ W.unop) at t
      change ((V.ι.appIso W.unop).inv r * t) •
          F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s =
        (V.ι.appIso W.unop).inv r •
          (t • F.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)
      exact mul_smul _ _ _)

/-- Over an open `W` of `V` the morphism attached to a section `s` of `F` over `V` multiplies a
function by the restriction of `s`. -/
theorem localSectionHom_app (V : X.Opens) (F : X.Modules) (s : Γ(F, V)) (W : V.toScheme.Opens)
    (r : Γ(X, V.ι ''ᵁ W)) :
    (localSectionHom V F s).val.app (Opposite.op W) r =
      r • F.presheaf.map (homOfLE (V.ι_image_le W)).op s := rfl

/-- The dictionary between sections and morphisms out of the structure sheaf is natural: pushing
a section along `f : F ⟶ G` corresponds to composing with the restriction of `f`. -/
theorem localSectionHom_natural (V : X.Opens) {F G : X.Modules} (s : Γ(F, V)) (f : F ⟶ G) :
    localSectionHom V F s ≫ (Scheme.Modules.restrictFunctor V.ι).map f =
      localSectionHom V G (f.val.app (Opposite.op V) s) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  change f.val.app (Opposite.op (V.ι ''ᵁ W))
      (r • F.presheaf.map (homOfLE (V.ι_image_le W)).op s) =
    r • G.presheaf.map (homOfLE (V.ι_image_le W)).op (f.val.app (Opposite.op V) s)
  have h1 := (f.val.app (Opposite.op (V.ι ''ᵁ W))).hom.map_smul r
    (F.presheaf.map (homOfLE (V.ι_image_le W)).op s)
  have h2 := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (X := X) f).naturality
      (homOfLE (V.ι_image_le W)).op) s
  exact h1.trans (congrArg (fun y : Γ(G, V.ι ''ᵁ W) => r • y) h2)

/-- The zero section corresponds to the zero morphism. -/
theorem localSectionHom_zero (V : X.Opens) (F : X.Modules) : localSectionHom V F 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  change r • F.presheaf.map (homOfLE (V.ι_image_le W)).op (0 : Γ(F, V)) = 0
  simp

/-- The dictionary between sections and morphisms out of the structure sheaf is additive. -/
theorem localSectionHom_add (V : X.Opens) (F : X.Modules) (s t : Γ(F, V)) :
    localSectionHom V F (s + t) = localSectionHom V F s + localSectionHom V F t := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  change r • F.presheaf.map (homOfLE (V.ι_image_le W)).op (s + t) =
    r • F.presheaf.map (homOfLE (V.ι_image_le W)).op s +
      r • F.presheaf.map (homOfLE (V.ι_image_le W)).op t
  simp [smul_add]

/-- The unit function of `V` corresponds to the identity of the structure sheaf of `V`. -/
theorem localSectionHom_one (V : X.Opens) :
    localSectionHom V (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, V)) = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  change (r : Γ(X, V.ι ''ᵁ W)) * X.presheaf.map (homOfLE (V.ι_image_le W)).op 1 = r
  simp

/-- A morphism out of the structure sheaf is linear over each open: it carries a product
`r * x` of functions to `r` times the image of `x`. -/
private lemma unit_hom_app_mul {F : X.Modules} (f : SheafOfModules.unit X.ringCatSheaf ⟶ F)
    (U : X.Opens) (r x : Γ(X, U)) :
    f.val.app (Opposite.op U) (r * x) =
      @SMul.smul Γ(X, U) Γ(F, U) _ r (f.val.app (Opposite.op U) x) :=
  (f.val.app (Opposite.op U)).hom.map_smul r x

/-- A morphism out of the structure sheaf is multiplication by the image of `1`: over an open
`U` it carries a function `r` to `r` times that image. -/
private lemma unit_hom_app_apply {F : X.Modules} (f : SheafOfModules.unit X.ringCatSheaf ⟶ F)
    (U : X.Opens) (r : Γ(X, U)) :
    f.val.app (Opposite.op U) r =
      @SMul.smul Γ(X, U) Γ(F, U) _ r (f.val.app (Opposite.op U) (1 : Γ(X, U))) := by
  have h := unit_hom_app_mul f U r 1
  rwa [mul_one] at h

/-- A morphism out of the structure sheaf is compatible with restriction on the image of `1`. -/
private lemma unit_hom_app_one_restrict {F : X.Modules} (f : SheafOfModules.unit X.ringCatSheaf ⟶ F)
    {V W : X.Opens} (hWV : W ≤ V) :
    F.presheaf.map (homOfLE hWV).op (f.val.app (Opposite.op V) (1 : Γ(X, V))) =
      f.val.app (Opposite.op W) (1 : Γ(X, W)) := by
  have h := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (X := X) f).naturality (homOfLE hWV).op) (1 : Γ(X, V))
  change f.val.app (Opposite.op W) (X.presheaf.map (homOfLE hWV).op (1 : Γ(X, V))) =
    F.presheaf.map (homOfLE hWV).op (f.val.app (Opposite.op V) (1 : Γ(X, V))) at h
  rw [map_one] at h
  exact h.symm

/-- The restriction to `V` of a morphism out of the structure sheaf of `X` is the morphism
attached to the section which is the image of `1 ∈ Γ(X, V)`. -/
theorem restrict_unit_hom_eq_localSectionHom (V : X.Opens) {F : X.Modules}
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (Scheme.Modules.restrictFunctor V.ι).map f =
      localSectionHom V F (f.val.app (Opposite.op V) (1 : Γ(X, V))) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  change f.val.app (Opposite.op (V.ι ''ᵁ W)) r =
    r • F.presheaf.map (homOfLE (V.ι_image_le W)).op (f.val.app (Opposite.op V) (1 : Γ(X, V)))
  rw [unit_hom_app_one_restrict f (V.ι_image_le W)]
  exact unit_hom_app_apply f (V.ι ''ᵁ W) r

/-- The scalar `c(1) ∈ Γ(X, V)` of an endomorphism `c` of the structure sheaf of `X`. -/
abbrev unitHomScalar (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (V : X.Opens) : Γ(X, V) := c.val.app (Opposite.op V) (1 : Γ(X, V))

/-- The scalars of an endomorphism of the structure sheaf form a compatible family: the one over
a smaller open is the restriction of the one over a bigger open. -/
theorem unitHomScalar_restrict
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    {V W : X.Opens} (hWV : W ≤ V) :
    X.presheaf.map (homOfLE hWV).op (unitHomScalar c V) = unitHomScalar c W := by
  exact unit_hom_app_one_restrict c hWV

/-- Precomposing with the restriction of an endomorphism `c` of the structure sheaf multiplies
the section by the scalar of `c` over `V`. -/
theorem localSectionHom_precomp (V : X.Opens) (F : X.Modules) (s : Γ(F, V))
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor V.ι).map c ≫ localSectionHom V F s =
      localSectionHom V F (unitHomScalar c V • s) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  have hm := F.val.map_smul (homOfLE (V.ι_image_le W)).op (unitHomScalar c V) s
  change F.presheaf.map (homOfLE (V.ι_image_le W)).op (unitHomScalar c V • s) =
    X.presheaf.map (homOfLE (V.ι_image_le W)).op (unitHomScalar c V) •
      F.presheaf.map (homOfLE (V.ι_image_le W)).op s at hm
  have hr := unit_hom_app_apply c (V.ι ''ᵁ W) r
  change c.val.app (Opposite.op (V.ι ''ᵁ W)) r = r * unitHomScalar c (V.ι ''ᵁ W) at hr
  change @SMul.smul Γ(X, V.ι ''ᵁ W) Γ(F, V.ι ''ᵁ W) _
      (c.val.app (Opposite.op (V.ι ''ᵁ W)) r)
      (F.presheaf.map (homOfLE (V.ι_image_le W)).op s) =
    r • F.presheaf.map (homOfLE (V.ι_image_le W)).op (unitHomScalar c V • s)
  rw [hm, unitHomScalar_restrict c (V.ι_image_le W), ← mul_smul, hr]
  rfl

/-- Distinct sections of `F` over `V` give distinct morphisms `𝒪_V ⟶ F|_V`. -/
theorem localSectionHom_injective (V : X.Opens) (F : X.Modules) :
    Function.Injective (localSectionHom V F) := by
  intro s t h
  have e := congrArg (fun f => f.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤))) h
  simp only [localSectionHom_app, one_smul] at e
  have : IsIso (homOfLE (V.ι_image_le (⊤ : V.toScheme.Opens))) := by
    rw [Subsingleton.elim (homOfLE (V.ι_image_le (⊤ : V.toScheme.Opens)))
      (eqToHom V.ι_image_top)]
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono (F.presheaf.map (homOfLE (V.ι_image_le
      (⊤ : V.toScheme.Opens))).op))) e

/-- A morphism out of the structure sheaf of an open subscheme `V` is multiplication by the
image of `1`: over an open `W` of `V` it carries a function `r` to `r` times that image. -/
private lemma restrict_unit_app_apply (V : X.Opens) {F : X.Modules}
    (e : Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) V.ι ⟶ F.restrict V.ι)
    (W : V.toScheme.Opens) (r : Γ(X, V.ι ''ᵁ W)) :
    e.val.app (Opposite.op W) r =
      @SMul.smul Γ(X, V.ι ''ᵁ W) Γ(F, V.ι ''ᵁ W) _ r
        (e.val.app (Opposite.op W) (1 : Γ(X, V.ι ''ᵁ W))) := by
  have hinv : (V.ι.appIso W).inv ((V.ι.appIso W).hom r) = r := Iso.hom_inv_id_apply _ _
  have h := (e.val.app (Opposite.op W)).hom.map_smul ((V.ι.appIso W).hom r)
    (1 : Γ(X, V.ι ''ᵁ W))
  change e.val.app (Opposite.op W)
      (@HMul.hMul Γ(X, V.ι ''ᵁ W) Γ(X, V.ι ''ᵁ W) Γ(X, V.ι ''ᵁ W) _
        ((V.ι.appIso W).inv ((V.ι.appIso W).hom r)) 1) =
    @SMul.smul Γ(X, V.ι ''ᵁ W) Γ(F, V.ι ''ᵁ W) _
      ((V.ι.appIso W).inv ((V.ι.appIso W).hom r))
      (e.val.app (Opposite.op W) (1 : Γ(X, V.ι ''ᵁ W))) at h
  rw [hinv] at h
  exact (congrArg (fun x : Γ(X, V.ι ''ᵁ W) => e.val.app (Opposite.op W) x)
    (mul_one r)).symm.trans h

/-- Every morphism `𝒪_V ⟶ F|_V` is multiplication by a section of `F` over `V`. -/
theorem localSectionHom_surjective (V : X.Opens) (F : X.Modules) :
    Function.Surjective (localSectionHom V F) := by
  intro e
  refine ⟨F.presheaf.map (eqToHom V.ι_image_top.symm).op
    (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤))), ?_⟩
  apply Scheme.Modules.hom_ext
  intro W
  ext r
  change Γ(X, V.ι ''ᵁ W) at r
  have hle : V.ι ''ᵁ W ≤ V.ι ''ᵁ (⊤ : V.toScheme.Opens) :=
    le_of_le_of_eq (V.ι_image_le W) V.ι_image_top.symm
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (X := V.toScheme) e).naturality
      (homOfLE (le_top : W ≤ (⊤ : V.toScheme.Opens))).op) (1 : Γ(X, V.ι ''ᵁ ⊤))
  change (e.val.app (Opposite.op W)
      (X.presheaf.map (homOfLE hle).op (1 : Γ(X, V.ι ''ᵁ ⊤))) : Γ(F, V.ι ''ᵁ W)) =
    F.presheaf.map (homOfLE hle).op
      (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤))) at hn
  rw [map_one] at hn
  have hh : (eqToHom V.ι_image_top.symm).op ≫ (homOfLE (V.ι_image_le W)).op =
      (homOfLE hle).op := Subsingleton.elim _ _
  have hz : (F.presheaf.map (homOfLE (V.ι_image_le W)).op
      (F.presheaf.map (eqToHom V.ι_image_top.symm).op
        (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤)))) : Γ(F, V.ι ''ᵁ W)) =
      e.val.app (Opposite.op W) (1 : Γ(X, V.ι ''ᵁ W)) :=
    (ConcreteCategory.congr_hom (F.presheaf.map_comp
      (eqToHom V.ι_image_top.symm).op (homOfLE (V.ι_image_le W)).op)
        (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤)))).symm.trans
      ((congrArg (fun g => F.presheaf.map g
        (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤)))) hh).trans hn.symm)
  have hr := restrict_unit_app_apply V e W r
  change (r • F.presheaf.map (homOfLE (V.ι_image_le W)).op
      (F.presheaf.map (eqToHom V.ι_image_top.symm).op
        (e.val.app (Opposite.op ⊤) (1 : Γ(X, V.ι ''ᵁ ⊤)))) : Γ(F, V.ι ''ᵁ W)) =
    e.val.app (Opposite.op W) r
  rw [hr]
  exact congrArg (fun y : Γ(F, V.ι ''ᵁ W) => r • y) hz

/-- A finite family of sections of `F` over `V`, read as a morphism `(𝒪_V)^ι ⟶ F|_V`: the `i`-th
coordinate is multiplication by `s i`. -/
def localFreeHom (V : X.Opens) (F : X.Modules) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (s : ι → Γ(F, V)) :
    Scheme.Modules.restrict (SheafOfModules.free (R := X.ringCatSheaf) ι) V.ι ⟶ F.restrict V.ι :=
  ∑ i, (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.freeProjection i) ≫
    localSectionHom V F (s i)

/-- Restricting a composite that equals `k` gives a composite of restrictions equal to the
restriction of `k`. -/
private lemma restrictFunctor_map_comp_eq (V : X.Opens) {A B C : X.Modules} (f : A ⟶ B)
    (g : B ⟶ C) {k : A ⟶ C} (h : f ≫ g = k) :
    (Scheme.Modules.restrictFunctor V.ι).map f ≫ (Scheme.Modules.restrictFunctor V.ι).map g =
      (Scheme.Modules.restrictFunctor V.ι).map k :=
  ((Scheme.Modules.restrictFunctor V.ι).map_comp _ _).symm.trans
    (congrArg (Scheme.Modules.restrictFunctor V.ι).map h)

/-- The `i`-th coordinate of the morphism attached to a finite family of sections is the
morphism attached to the `i`-th section. -/
theorem localFreeHom_ι (V : X.Opens) (F : X.Modules) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (s : ι → Γ(F, V)) (i : ι) :
    (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.ιFree i) ≫ localFreeHom V F s =
      localSectionHom V F (s i) := by
  have hself := (restrictFunctor_map_comp_eq V _ _
    (SheafOfModules.ιFree_comp_freeProjection_self (R := X.ringCatSheaf) i)).trans
      ((Scheme.Modules.restrictFunctor V.ι).map_id _)
  have hne : ∀ b : ι, b ≠ i → (Scheme.Modules.restrictFunctor V.ι).map
      (SheafOfModules.ιFree i) ≫ (Scheme.Modules.restrictFunctor V.ι).map
        (SheafOfModules.freeProjection (R := X.ringCatSheaf) b) = 0 := fun b hb =>
    (restrictFunctor_map_comp_eq V _ _
      (SheafOfModules.ιFree_comp_freeProjection_of_ne (Ne.symm hb))).trans
        (Functor.map_zero _ _ _)
  simp only [localFreeHom, Preadditive.comp_sum, ← Category.assoc]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun b _ hb => by rw [hne b hb, zero_comp],
    hself, Category.id_comp]

/-- Precomposing the morphism of a finite family with the restriction of `c : 𝒪_X ⟶ (𝒪_X)^ι`
gives the morphism of the single section which is the corresponding linear combination. -/
theorem localFreeHom_precomp (V : X.Opens) (F : X.Modules) {ι : Type u} [Fintype ι]
    [DecidableEq ι] (s : ι → Γ(F, V))
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    (Scheme.Modules.restrictFunctor V.ι).map c ≫ localFreeHom V F s =
      localSectionHom V F (∑ i, unitHomScalar (c ≫ SheafOfModules.freeProjection i) V • s i) := by
  have hp : ∀ i : ι, (Scheme.Modules.restrictFunctor V.ι).map c ≫
      ((Scheme.Modules.restrictFunctor V.ι).map
        (SheafOfModules.freeProjection (R := X.ringCatSheaf) i) ≫
          localSectionHom V F (s i)) =
      localSectionHom V F (unitHomScalar (c ≫ SheafOfModules.freeProjection i) V • s i) :=
    fun i => (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ localSectionHom V F (s i))
        ((Scheme.Modules.restrictFunctor V.ι).map_comp c
          (SheafOfModules.freeProjection i)).symm).trans
        (localSectionHom_precomp V F (s i) (c ≫ SheafOfModules.freeProjection i)))
  simp only [localFreeHom, Preadditive.comp_sum, hp]
  let f : Γ(F, V) →+
      (Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) V.ι ⟶ F.restrict V.ι) :=
    { toFun := localSectionHom V F
      map_zero' := localSectionHom_zero V F
      map_add' := localSectionHom_add V F }
  exact (map_sum f _ _).symm

/-- A morphism out of `(𝒪_V)^ι` is determined by its `ι` coordinates. -/
theorem localFreeHom_ext (V : X.Opens) {F : V.toScheme.Modules} {ι : Type u} [Finite ι]
    {f g : Scheme.Modules.restrict (SheafOfModules.free (R := X.ringCatSheaf) ι) V.ι ⟶ F}
    (h : ∀ i, (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.ιFree i) ≫ f =
      (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.ιFree i) ≫ g) : f = g := by
  classical
  have := Fintype.ofFinite ι
  have e : (∑ i : ι, (Scheme.Modules.restrictFunctor V.ι).map
      (SheafOfModules.freeProjection (R := X.ringCatSheaf) i) ≫
        (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.ιFree i)) = 𝟙 _ := by
    simp only [fun i => restrictFunctor_map_comp_eq V
      (SheafOfModules.freeProjection (R := X.ringCatSheaf) i) (SheafOfModules.ιFree i) rfl]
    exact ((Scheme.Modules.restrictFunctor V.ι).map_sum _ _).symm.trans
      ((congrArg (fun q => (Scheme.Modules.restrictFunctor V.ι).map q)
        (SheafOfModules.sum_freeProjection_comp_ιFree (R := X.ringCatSheaf) (I := ι))).trans
          ((Scheme.Modules.restrictFunctor V.ι).map_id _))
  calc
    f = (∑ i : ι, (Scheme.Modules.restrictFunctor V.ι).map
        (SheafOfModules.freeProjection (R := X.ringCatSheaf) i) ≫
          (Scheme.Modules.restrictFunctor V.ι).map (SheafOfModules.ιFree i)) ≫ f := by
      rw [e, Category.id_comp]
    _ = _ := by
      simp only [Preadditive.sum_comp, Category.assoc, h]
      simp_rw [← Category.assoc]
      rw [← Preadditive.sum_comp, e, Category.id_comp]

/-- Restricting a linear combination of sections restricts both the coefficients and the
sections. -/
theorem restrict_linearCombination {ι : Type u} [Fintype ι] (F : X.Modules)
    {V W : X.Opens} (hWV : W ≤ V) (t : ι → Γ(F, V))
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    F.presheaf.map (homOfLE hWV).op
        (∑ i, unitHomScalar (c ≫ SheafOfModules.freeProjection i) V • t i) =
      ∑ i, unitHomScalar (c ≫ SheafOfModules.freeProjection i) W •
        F.presheaf.map (homOfLE hWV).op (t i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul, unitHomScalar_restrict]

end Stacks.AlgebraicGeometry.LocalSection

end
