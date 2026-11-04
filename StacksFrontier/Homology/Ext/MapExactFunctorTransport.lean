module

public import StacksFrontier.Homology.Ext.MapExactFunctorComp
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transporting `Ext` diagrams along squares of exact functors

Let `P : 𝒞₁ ⥤ 𝒞₂` and `Q : 𝒟₁ ⥤ 𝒟₂` be exact functors between abelian categories, and let
`L₁ : 𝒟₁ ⥤ 𝒞₁`, `L₂ : 𝒟₂ ⥤ 𝒞₂` be exact functors with an isomorphism `θ : Q ⋙ L₂ ≅ L₁ ⋙ P`.
A map on `Ext` of the shape "apply `Q`, then precompose and postcompose with given morphisms" is
carried by `L₁`, `L₂` to the map of the same shape built from `P`, as soon as the four
morphisms involved are compatible through `θ` (`extConj_mapExactFunctor_square`).

When the `L`s are left adjoints `L₁ ⊣ E₁`, `L₂ ⊣ E₂`, `P ⊣ P'` and `Q ⊣ Q'`, the isomorphism `θ`
is taken to be the conjugate of an isomorphism `σ : E₂ ⋙ Q' ≅ P' ⋙ E₁` of right adjoints
(`squareIso`), and the compatibility of a morphism with `θ` is equivalent to the compatibility
of its transpose with `σ` (`comp_counit_eq_squareIso_hom_app_comp_iff`).

## Main results

* `Stacks.Homology.extConj_mapExactFunctor_square` — the naturality square.
* `Stacks.Homology.squareIso` and `Stacks.Homology.comp_counit_eq_squareIso_hom_app_comp_iff`.
* `Stacks.Homology.bijective_mapExactFunctor_of_equivalence` — `Ext` along an equivalence is
  bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Stacks.Homology

/-- Conjugating by isomorphisms is a bijection. -/
private theorem bijective_extConj_of_iso {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
    {X' X Y Y' : C} (eX : X' ≅ X) (eY : Y ≅ Y') (n : ℕ) :
    Function.Bijective (extConj eX.hom eY.hom : Ext.{w} X Y n → Ext.{w} X' Y' n) := by
  refine ⟨fun y y' h => ?_, fun z => ⟨extConj eX.inv eY.inv z, ?_⟩⟩
  · simpa [extConj_extConj, extConj_id] using congrArg (extConj eX.inv eY.inv) h
  · simp [extConj_extConj, extConj_id]

/-- An equivalence of abelian categories is additive and preserves finite limits and colimits. -/
private theorem additive_and_preserves_finite_of_isEquivalence {C : Type u₁} [Category.{v₁} C]
    [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.IsEquivalence] :
    F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  have : PreservesLimitsOfSize.{0, 0} F := Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimitsOfSize.{0, 0} F := Adjunction.isEquivalence_preservesColimits _
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact ⟨Functor.additive_of_preserves_binary_products _, ⟨fun _ _ _ => inferInstance⟩,
    ⟨fun _ _ _ => inferInstance⟩⟩

section Square

variable {𝒞₁ : Type u₁} [Category.{v₁} 𝒞₁] [Abelian 𝒞₁] {𝒞₂ : Type u₂} [Category.{v₂} 𝒞₂]
  [Abelian 𝒞₂] {𝒟₁ : Type u₃} [Category.{v₃} 𝒟₁] [Abelian 𝒟₁] {𝒟₂ : Type u₄}
  [Category.{v₄} 𝒟₂] [Abelian 𝒟₂]
  [HasExt.{w} 𝒞₁] [HasExt.{w} 𝒞₂] [HasExt.{w'} 𝒟₁] [HasExt.{w'} 𝒟₂] [EnoughInjectives 𝒟₁]

/-- **`Ext` along a square of exact functors.** For `θ : Q ⋙ L₂ ≅ L₁ ⋙ P` and morphisms
compatible through `θ`, carrying a class along `Q` and conjugating it, then along `L₂` and
conjugating, is carrying it along `L₁` and conjugating, then along `P` and conjugating. -/
theorem extConj_mapExactFunctor_square
    (P : 𝒞₁ ⥤ 𝒞₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : 𝒟₁ ⥤ 𝒟₂) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (L₁ : 𝒟₁ ⥤ 𝒞₁) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : 𝒟₂ ⥤ 𝒞₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits (Q ⋙ L₂)] [PreservesFiniteColimits (Q ⋙ L₂)]
    [PreservesFiniteLimits (L₁ ⋙ P)] [PreservesFiniteColimits (L₁ ⋙ P)]
    (θ : Q ⋙ L₂ ≅ L₁ ⋙ P)
    {Z₁ G₁ : 𝒞₁} {Z₂ G₂ : 𝒞₂} (a : Z₂ ⟶ P.obj Z₁) (b : P.obj G₁ ⟶ G₂)
    {A₁ F₁ : 𝒟₁} {A₂ F₂ : 𝒟₂} (a' : A₂ ⟶ Q.obj A₁) (b' : Q.obj F₁ ⟶ F₂)
    (ζ₁ : Z₁ ⟶ L₁.obj A₁) (γ₁ : L₁.obj F₁ ⟶ G₁) (ζ₂ : Z₂ ⟶ L₂.obj A₂) (γ₂ : L₂.obj F₂ ⟶ G₂)
    (ha : ζ₂ ≫ L₂.map a' ≫ θ.hom.app A₁ = a ≫ P.map ζ₁)
    (hb : θ.inv.app F₁ ≫ L₂.map b' ≫ γ₂ = P.map γ₁ ≫ b) {n : ℕ} (x : Ext.{w'} A₁ F₁ n) :
    extConj ζ₂ γ₂ ((extConj a' b' (x.mapExactFunctor Q :
        Ext.{w'} (Q.obj A₁) (Q.obj F₁) n)).mapExactFunctor L₂ :
        Ext.{w} (L₂.obj A₂) (L₂.obj F₂) n) =
      extConj a b ((extConj ζ₁ γ₁ (x.mapExactFunctor L₁ :
        Ext.{w} (L₁.obj A₁) (L₁.obj F₁) n)).mapExactFunctor P :
        Ext.{w} (P.obj Z₁) (P.obj G₁) n) := by
  have ha' : ζ₂ ≫ L₂.map a' ≫ θ.symm.inv.app A₁ = a ≫ P.map ζ₁ := ha
  have hb' : θ.symm.hom.app F₁ ≫ L₂.map b' ≫ γ₂ = P.map γ₁ ≫ b := hb
  rw [extConj_mapExactFunctor, extConj_mapExactFunctor, extConj_extConj, extConj_extConj,
    ← ext_mapExactFunctor_comp_functor Q L₂, ← ext_mapExactFunctor_comp_functor L₁ P,
    ext_mapExactFunctor_of_iso' (L₁ ⋙ P) (Q ⋙ L₂) θ.symm x, extConj_extConj]
  simp only [Category.assoc] at ha' hb' ⊢
  rw [ha', hb']

end Square

section Conjugate

variable {𝒞₁ : Type u₁} [Category.{v₁} 𝒞₁] {𝒞₂ : Type u₂} [Category.{v₂} 𝒞₂]
  {𝒟₁ : Type u₃} [Category.{v₃} 𝒟₁] {𝒟₂ : Type u₄} [Category.{v₄} 𝒟₂]
  {P : 𝒞₁ ⥤ 𝒞₂} {P' : 𝒞₂ ⥤ 𝒞₁} (adjP : P ⊣ P') {Q : 𝒟₁ ⥤ 𝒟₂} {Q' : 𝒟₂ ⥤ 𝒟₁} (adjQ : Q ⊣ Q')
  {L₁ : 𝒟₁ ⥤ 𝒞₁} {E₁ : 𝒞₁ ⥤ 𝒟₁} (adj₁ : L₁ ⊣ E₁) {L₂ : 𝒟₂ ⥤ 𝒞₂} {E₂ : 𝒞₂ ⥤ 𝒟₂}
  (adj₂ : L₂ ⊣ E₂)

/-- **The square of left adjoints conjugate to a square of right adjoints.** From
`σ : E₂ ⋙ Q' ≅ P' ⋙ E₁` the isomorphism `Q ⋙ L₂ ≅ L₁ ⋙ P` of left adjoints, under the composite
adjunctions `Q ⋙ L₂ ⊣ E₂ ⋙ Q'` and `L₁ ⋙ P ⊣ P' ⋙ E₁`. -/
def squareIso (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁) : Q ⋙ L₂ ≅ L₁ ⋙ P :=
  (conjugateIsoEquiv (adj₁.comp adjP) (adjQ.comp adj₂)).symm σ.symm

/-- The conjugate of `(squareIso adjP adjQ adj₁ adj₂ σ).hom` under the composite adjunctions is
`σ.inv`. -/
theorem conjugateEquiv_squareIso_hom (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁) :
    conjugateEquiv (adj₁.comp adjP) (adjQ.comp adj₂) (squareIso adjP adjQ adj₁ adj₂ σ).hom =
      σ.inv := by
  show (conjugateIsoEquiv (adj₁.comp adjP) (adjQ.comp adj₂)
    ((conjugateIsoEquiv (adj₁.comp adjP) (adjQ.comp adj₂)).symm σ.symm)).hom = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [Category.{v₁} 𝒞₁] in
/-- Transposing across a natural transformation of left adjoints. -/
theorem homEquiv_app_comp {C D : Type*} [Category C] [Category D] {F₁ F₂ : C ⥤ D}
    {G₁ G₂ : D ⥤ C} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (α : F₂ ⟶ F₁) {X : C} {Y : D}
    (h : F₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ h) =
      adj₁.homEquiv X Y h ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv adj₁ adj₂ α X, Category.assoc, Category.assoc]
  congr 1
  exact ((conjugateEquiv adj₁ adj₂ α).naturality h).symm

/-- **Compatibility with the square of left adjoints is compatibility of the transpose with the
square of right adjoints.** -/
theorem comp_counit_eq_squareIso_hom_app_comp_iff (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁) {X : 𝒟₁} {G₂ : 𝒞₂}
    (g : Q.obj X ⟶ E₂.obj G₂) (h : P.obj (L₁.obj X) ⟶ G₂) :
    L₂.map g ≫ adj₂.counit.app G₂ = (squareIso adjP adjQ adj₁ adj₂ σ).hom.app X ≫ h ↔
      adjQ.homEquiv _ _ g = (adj₁.comp adjP).homEquiv _ _ h ≫ σ.inv.app G₂ := by
  rw [← (adjQ.comp adj₂).homEquiv _ _ |>.apply_eq_iff_eq, homEquiv_app_comp (adj₁.comp adjP)
    (adjQ.comp adj₂), conjugateEquiv_squareIso_hom, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.comp_id,
    Functor.id_obj]

/-- **A transported transition is compatible with the square.** If the transpose of `b'` is the
image under `E₁` of the transpose of `b`, followed by `σ`, then `b'` and `b` are compatible
through `squareIso`, the counits identifying `L₁ E₁` and `L₂ E₂` with the identity. -/
theorem squareIso_inv_app_comp_map_comp_counit (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁) {G₁ : 𝒞₁} {G₂ : 𝒞₂}
    (b : P.obj G₁ ⟶ G₂) (b' : Q.obj (E₁.obj G₁) ⟶ E₂.obj G₂)
    (hb' : adjQ.homEquiv _ _ b' = E₁.map (adjP.homEquiv _ _ b) ≫ σ.inv.app G₂) :
    (squareIso adjP adjQ adj₁ adj₂ σ).inv.app (E₁.obj G₁) ≫ L₂.map b' ≫ adj₂.counit.app G₂ =
      P.map (adj₁.counit.app G₁) ≫ b := by
  rw [← cancel_epi ((squareIso adjP adjQ adj₁ adj₂ σ).hom.app (E₁.obj G₁)),
    Iso.hom_inv_id_app_assoc, comp_counit_eq_squareIso_hom_app_comp_iff, hb']
  refine congrArg (· ≫ σ.inv.app G₂) ?_
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_unit (adj := adj₁), Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]
  rfl

end Conjugate

section Equivalence

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] [Abelian 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  [Abelian 𝒟] [HasExt.{w} 𝒞] [HasExt.{w'} 𝒟] [EnoughInjectives 𝒞] [EnoughInjectives 𝒟]
  (e : 𝒞 ≌ 𝒟) [e.functor.Additive] [PreservesFiniteLimits e.functor]
  [PreservesFiniteColimits e.functor] [e.inverse.Additive] [PreservesFiniteLimits e.inverse]
  [PreservesFiniteColimits e.inverse]

omit [EnoughInjectives 𝒟] in
/-- `Ext` along an equivalence followed by `Ext` along its inverse, conjugated by the unit, is
the identity. -/
theorem extConj_mapExactFunctor_inverse_mapExactFunctor_functor (A B : 𝒞) {n : ℕ}
    (x : Ext.{w} A B n) :
    extConj (e.unitIso.hom.app A) (e.unitIso.inv.app B)
      ((x.mapExactFunctor e.functor :
        Ext.{w'} (e.functor.obj A) (e.functor.obj B) n).mapExactFunctor
        e.inverse : Ext.{w} (e.inverse.obj (e.functor.obj A)) (e.inverse.obj (e.functor.obj B)) n) =
      x := by
  rw [← ext_mapExactFunctor_comp_functor e.functor e.inverse,
    ext_mapExactFunctor_of_iso' (𝟭 𝒞) (e.functor ⋙ e.inverse) e.unitIso x,
    ext_mapExactFunctor_id, extConj_extConj]
  simp only [Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  exact extConj_id x

omit [EnoughInjectives 𝒟] in
/-- `Ext` along an equivalence is injective. -/
theorem injective_mapExactFunctor_of_equivalence (A B : 𝒞) (n : ℕ) :
    Function.Injective (fun x : Ext.{w} A B n =>
      (x.mapExactFunctor e.functor : Ext.{w'} (e.functor.obj A) (e.functor.obj B) n)) := by
  intro x y hxy
  simp only at hxy
  rw [← extConj_mapExactFunctor_inverse_mapExactFunctor_functor e A B x,
    ← extConj_mapExactFunctor_inverse_mapExactFunctor_functor e A B y, hxy]

/-- **`Ext` along an equivalence is bijective.** -/
theorem bijective_mapExactFunctor_of_equivalence (A B : 𝒞) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w} A B n =>
      (x.mapExactFunctor e.functor : Ext.{w'} (e.functor.obj A) (e.functor.obj B) n)) := by
  refine ⟨injective_mapExactFunctor_of_equivalence e A B n, fun y => ?_⟩
  refine ⟨extConj (e.unitIso.hom.app A) (e.unitIso.inv.app B)
    (y.mapExactFunctor e.inverse : Ext.{w} (e.inverse.obj (e.functor.obj A))
      (e.inverse.obj (e.functor.obj B)) n), ?_⟩
  have hinv : Function.Injective (fun z : Ext.{w'} (e.functor.obj A) (e.functor.obj B) n =>
      extConj (e.unitIso.hom.app A) (e.unitIso.inv.app B)
        (z.mapExactFunctor e.inverse : Ext.{w} (e.inverse.obj (e.functor.obj A))
          (e.inverse.obj (e.functor.obj B)) n)) := by
    intro z₁ z₂ h
    have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
    have : PreservesFiniteLimits e.symm.functor :=
      inferInstanceAs (PreservesFiniteLimits e.inverse)
    have : PreservesFiniteColimits e.symm.functor :=
      inferInstanceAs (PreservesFiniteColimits e.inverse)
    have : e.symm.inverse.Additive := inferInstanceAs e.functor.Additive
    have : PreservesFiniteLimits e.symm.inverse :=
      inferInstanceAs (PreservesFiniteLimits e.functor)
    have : PreservesFiniteColimits e.symm.inverse :=
      inferInstanceAs (PreservesFiniteColimits e.functor)
    exact injective_mapExactFunctor_of_equivalence e.symm _ _ n
      ((bijective_extConj_of_iso (e.unitIso.app A) (e.unitIso.app B).symm n).1 h)
  exact hinv (extConj_mapExactFunctor_inverse_mapExactFunctor_functor e A B _)

end Equivalence

section Compare

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]

/-- **`Ext` read through a left adjoint with invertible counit**: a class between `E N` and `E M`
carried along `L` and conjugated by the counit, a class between `N` and `M`. -/
def extCompareAlong [Abelian 𝒞] [Abelian 𝒟] [HasExt.{w} 𝒞] [HasExt.{w'} 𝒟]
    [EnoughInjectives 𝒟] {E : 𝒞 ⥤ 𝒟} {L : 𝒟 ⥤ 𝒞} (adj : L ⊣ E) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [IsIso adj.counit] (N M : 𝒞) {n : ℕ}
    (x : Ext.{w'} (E.obj N) (E.obj M) n) : Ext.{w} N M n :=
  extConj (inv (adj.counit.app N)) (adj.counit.app M)
    (x.mapExactFunctor L : Ext.{w} (L.obj (E.obj N)) (L.obj (E.obj M)) n)

/-- `extCompareAlong` as a morphism of groups. -/
def extCompareAlongHom [Abelian 𝒞] [Abelian 𝒟] [HasExt.{w} 𝒞] [HasExt.{w'} 𝒟]
    [EnoughInjectives 𝒟] {E : 𝒞 ⥤ 𝒟} {L : 𝒟 ⥤ 𝒞} (adj : L ⊣ E) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [IsIso adj.counit] (N M : 𝒞) (n : ℕ) :
    Ext.{w'} (E.obj N) (E.obj M) n →+ Ext.{w} N M n :=
  (extConjHom (inv (adj.counit.app N)) (adj.counit.app M) n).comp (L.mapExtAddHom _ _ n)

/-- `extCompareAlongHom adj N M n` sends `x` to `extCompareAlong adj N M x`. -/
theorem extCompareAlongHom_apply [Abelian 𝒞] [Abelian 𝒟] [HasExt.{w} 𝒞] [HasExt.{w'} 𝒟]
    [EnoughInjectives 𝒟] {E : 𝒞 ⥤ 𝒟} {L : 𝒟 ⥤ 𝒞} (adj : L ⊣ E) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [IsIso adj.counit] (N M : 𝒞) (n : ℕ)
    (x : Ext.{w'} (E.obj N) (E.obj M) n) :
    extCompareAlongHom adj N M n x = extCompareAlong adj N M x := rfl

/-- **`Ext` read through a left adjoint which is an equivalence is bijective.** -/
theorem bijective_extCompareAlong [Abelian 𝒞] [Abelian 𝒟] [HasExt.{w} 𝒞]
    [HasExt.{w'} 𝒟] [EnoughInjectives 𝒞] [EnoughInjectives 𝒟] {E : 𝒞 ⥤ 𝒟} {L : 𝒟 ⥤ 𝒞}
    (adj : L ⊣ E) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [IsIso adj.unit] [IsIso adj.counit] (N M : 𝒞) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w'} (E.obj N) (E.obj M) n => extCompareAlong adj N M x) := by
  let e : 𝒟 ≌ 𝒞 := adj.toEquivalence
  obtain ⟨_, _, _⟩ := additive_and_preserves_finite_of_isEquivalence e.inverse
  have : e.functor.Additive := ‹L.Additive›
  have : PreservesFiniteLimits e.functor := ‹PreservesFiniteLimits L›
  have : PreservesFiniteColimits e.functor := ‹PreservesFiniteColimits L›
  have hb := bijective_mapExactFunctor_of_equivalence.{w', w} e (E.obj N) (E.obj M) n
  exact (bijective_extConj_of_iso (asIso (adj.counit.app N)).symm
    (asIso (adj.counit.app M)) n).comp hb

end Compare

section SquareIso

variable {𝒞₁ : Type u₁} [Category.{v₁} 𝒞₁] [Abelian 𝒞₁] {𝒞₂ : Type u₂} [Category.{v₂} 𝒞₂]
  [Abelian 𝒞₂] {𝒟₁ : Type u₃} [Category.{v₃} 𝒟₁] [Abelian 𝒟₁] {𝒟₂ : Type u₄}
  [Category.{v₄} 𝒟₂] [Abelian 𝒟₂]
  [HasExt.{w} 𝒞₁] [HasExt.{w} 𝒞₂] [HasExt.{w'} 𝒟₁] [HasExt.{w'} 𝒟₂] [EnoughInjectives 𝒟₁]

/-- **`Ext` transported along a square of right adjoints, for two variables transported the same
way.** If `σ : E₂ ⋙ Q' ≅ P' ⋙ E₁` is a square of right adjoints, `L₁ ⊣ E₁` and `L₂ ⊣ E₂` have
invertible counits, and the transitions `b'N`, `b'M` in the `𝒟`-world are the transports of
`bN`, `bM` in the `𝒞`-world through `σ`, then reading `Ext` in the `𝒞`-world through the counits
carries `Q` followed by `b'N⁻¹, b'M` to `P` followed by `bN⁻¹, bM`. -/
theorem extConj_mapExactFunctor_squareIso
    (P : 𝒞₁ ⥤ 𝒞₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {P' : 𝒞₂ ⥤ 𝒞₁} (adjP : P ⊣ P')
    (Q : 𝒟₁ ⥤ 𝒟₂) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    {Q' : 𝒟₂ ⥤ 𝒟₁} (adjQ : Q ⊣ Q')
    {E₁ : 𝒞₁ ⥤ 𝒟₁} {E₂ : 𝒞₂ ⥤ 𝒟₂} {L₁ : 𝒟₁ ⥤ 𝒞₁} (adj₁ : L₁ ⊣ E₁) {L₂ : 𝒟₂ ⥤ 𝒞₂}
    (adj₂ : L₂ ⊣ E₂) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [IsIso adj₁.counit] [IsIso adj₂.counit] (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁)
    {N₁ M₁ : 𝒞₁} {N₂ M₂ : 𝒞₂} (bN : P.obj N₁ ⟶ N₂) (ibN : IsIso bN) (bM : P.obj M₁ ⟶ M₂)
    (b'N : Q.obj (E₁.obj N₁) ⟶ E₂.obj N₂) (ib'N : IsIso b'N) (b'M : Q.obj (E₁.obj M₁) ⟶ E₂.obj M₂)
    (hN : adjQ.homEquiv _ _ b'N = E₁.map (adjP.homEquiv _ _ bN) ≫ σ.inv.app N₂)
    (hM : adjQ.homEquiv _ _ b'M = E₁.map (adjP.homEquiv _ _ bM) ≫ σ.inv.app M₂)
    {n : ℕ} (x : Ext.{w'} (E₁.obj N₁) (E₁.obj M₁) n) :
    haveI := ibN; haveI := ib'N
    extConj (inv (adj₂.counit.app N₂)) (adj₂.counit.app M₂)
        ((extConj (inv b'N) b'M (x.mapExactFunctor Q :
          Ext.{w'} (Q.obj (E₁.obj N₁)) (Q.obj (E₁.obj M₁)) n)).mapExactFunctor L₂ :
          Ext.{w} (L₂.obj (E₂.obj N₂)) (L₂.obj (E₂.obj M₂)) n) =
      extConj (inv bN) bM ((extConj (inv (adj₁.counit.app N₁)) (adj₁.counit.app M₁)
        (x.mapExactFunctor L₁ :
          Ext.{w} (L₁.obj (E₁.obj N₁)) (L₁.obj (E₁.obj M₁)) n)).mapExactFunctor
          P : Ext.{w} (P.obj N₁) (P.obj M₁) n) := by
  have := ibN; have := ib'N
  let θ := squareIso adjP adjQ adj₁ adj₂ σ
  have : PreservesFiniteLimits (Q ⋙ L₂) := comp_preservesFiniteLimits Q L₂
  have : PreservesFiniteColimits (Q ⋙ L₂) := comp_preservesFiniteColimits Q L₂
  have : PreservesFiniteLimits (L₁ ⋙ P) := comp_preservesFiniteLimits L₁ P
  have : PreservesFiniteColimits (L₁ ⋙ P) := comp_preservesFiniteColimits L₁ P
  have hbN := squareIso_inv_app_comp_map_comp_counit adjP adjQ adj₁ adj₂ σ bN b'N hN
  have hbM := squareIso_inv_app_comp_map_comp_counit adjP adjQ adj₁ adj₂ σ bM b'M hM
  refine extConj_mapExactFunctor_square P Q L₁ L₂ θ (inv bN) bM (inv b'N) b'M
    (inv (adj₁.counit.app N₁)) (adj₁.counit.app M₁) (inv (adj₂.counit.app N₂))
    (adj₂.counit.app M₂) ?_ hbM x
  calc inv (adj₂.counit.app N₂) ≫ L₂.map (inv b'N) ≫ θ.hom.app (E₁.obj N₁)
      = inv (θ.inv.app (E₁.obj N₁) ≫ L₂.map b'N ≫ adj₂.counit.app N₂) := by
        simp [IsIso.inv_comp, Functor.map_inv]
    _ = inv (P.map (adj₁.counit.app N₁) ≫ bN) := (IsIso.inv_eq_inv).2 hbN
    _ = inv bN ≫ P.map (inv (adj₁.counit.app N₁)) := by
        simp [IsIso.inv_comp, Functor.map_inv]

/-- `extConj_mapExactFunctor_squareIso` with the abelian structures and `Ext` instances of the four
categories taken by unification. -/
theorem extConj_mapExactFunctor_squareIso' {𝒞₁ : Type u₁} [Category.{v₁} 𝒞₁] {𝒞₂ : Type u₂}
    [Category.{v₂} 𝒞₂] {𝒟₁ : Type u₃} [Category.{v₃} 𝒟₁] {𝒟₂ : Type u₄} [Category.{v₄} 𝒟₂]
    {_ : Abelian 𝒞₁} {_ : Abelian 𝒞₂} {_ : Abelian 𝒟₁} {_ : Abelian 𝒟₂}
    {_ : HasExt.{w} 𝒞₁} {_ : HasExt.{w} 𝒞₂} {_ : HasExt.{w'} 𝒟₁} {_ : HasExt.{w'} 𝒟₂}
    [EnoughInjectives 𝒟₁]
    (P : 𝒞₁ ⥤ 𝒞₂) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {P' : 𝒞₂ ⥤ 𝒞₁} (adjP : P ⊣ P')
    (Q : 𝒟₁ ⥤ 𝒟₂) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    {Q' : 𝒟₂ ⥤ 𝒟₁} (adjQ : Q ⊣ Q')
    {E₁ : 𝒞₁ ⥤ 𝒟₁} {E₂ : 𝒞₂ ⥤ 𝒟₂} {L₁ : 𝒟₁ ⥤ 𝒞₁} (adj₁ : L₁ ⊣ E₁) {L₂ : 𝒟₂ ⥤ 𝒞₂}
    (adj₂ : L₂ ⊣ E₂) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [IsIso adj₁.counit] [IsIso adj₂.counit] (σ : E₂ ⋙ Q' ≅ P' ⋙ E₁)
    {N₁ M₁ : 𝒞₁} {N₂ M₂ : 𝒞₂} (bN : P.obj N₁ ⟶ N₂) (ibN : IsIso bN) (bM : P.obj M₁ ⟶ M₂)
    (b'N : Q.obj (E₁.obj N₁) ⟶ E₂.obj N₂) (ib'N : IsIso b'N) (b'M : Q.obj (E₁.obj M₁) ⟶ E₂.obj M₂)
    (hN : adjQ.homEquiv _ _ b'N = E₁.map (adjP.homEquiv _ _ bN) ≫ σ.inv.app N₂)
    (hM : adjQ.homEquiv _ _ b'M = E₁.map (adjP.homEquiv _ _ bM) ≫ σ.inv.app M₂)
    {n : ℕ} (x : Ext.{w'} (E₁.obj N₁) (E₁.obj M₁) n) :
    haveI := ibN; haveI := ib'N
    extConj (inv (adj₂.counit.app N₂)) (adj₂.counit.app M₂)
        ((extConj (inv b'N) b'M (x.mapExactFunctor Q :
          Ext.{w'} (Q.obj (E₁.obj N₁)) (Q.obj (E₁.obj M₁)) n)).mapExactFunctor L₂ :
          Ext.{w} (L₂.obj (E₂.obj N₂)) (L₂.obj (E₂.obj M₂)) n) =
      extConj (inv bN) bM ((extConj (inv (adj₁.counit.app N₁)) (adj₁.counit.app M₁)
        (x.mapExactFunctor L₁ :
          Ext.{w} (L₁.obj (E₁.obj N₁)) (L₁.obj (E₁.obj M₁)) n)).mapExactFunctor
          P : Ext.{w} (P.obj N₁) (P.obj M₁) n) :=
  extConj_mapExactFunctor_squareIso P adjP Q adjQ adj₁ adj₂ σ bN ibN bM b'N ib'N b'M hN hM x

end SquareIso

section Vanishing

universe w₁ w₂ w₃ w₄

/-- A type with an injective map to a subsingleton is a subsingleton. -/
theorem subsingleton_of_injective {α : Sort*} {β : Sort*} {f : α → β}
    (hf : Function.Injective f) [Subsingleton β] : Subsingleton α :=
  hf.subsingleton

/-- The image of a surjective map out of a subsingleton is a subsingleton. -/
theorem subsingleton_of_surjective {α : Sort*} {β : Sort*} {f : α → β}
    (hf : Function.Surjective f) [Subsingleton α] : Subsingleton β :=
  hf.subsingleton

/-- `Ext` groups between isomorphic objects vanish together. -/
theorem subsingleton_ext_of_iso {𝒞 : Type w₁} [Category.{w₂} 𝒞] {_ : Abelian 𝒞} [HasExt.{w₃} 𝒞]
    {A A' B B' : 𝒞} (eA : A ≅ A') (eB : B ≅ B') {n : ℕ}
    (h : Subsingleton (Ext.{w₃} A' B' n)) : Subsingleton (Ext.{w₃} A B n) := by
  exact (bijective_extConj_of_iso eA eB.symm n).2.subsingleton

/-- **`Ext` groups vanish together along a functor which is an equivalence.** -/
theorem subsingleton_ext_iff_of_isEquivalence {𝒞 : Type w₁} [Category.{w₂} 𝒞] {_ : Abelian 𝒞}
    {𝒟 : Type w₃} [Category.{w₄} 𝒟] {_ : Abelian 𝒟} {_ : HasExt.{w} 𝒞} {_ : HasExt.{w'} 𝒟}
    [EnoughInjectives 𝒞] [EnoughInjectives 𝒟] (F : 𝒞 ⥤ 𝒟) (hF : F.IsEquivalence) (A B : 𝒞)
    (n : ℕ) :
    Subsingleton (Ext.{w} A B n) ↔ Subsingleton (Ext.{w'} (F.obj A) (F.obj B) n) := by
  let e := F.asEquivalence
  obtain ⟨_, _, _⟩ := additive_and_preserves_finite_of_isEquivalence e.functor
  obtain ⟨_, _, _⟩ := additive_and_preserves_finite_of_isEquivalence e.inverse
  have hb := bijective_mapExactFunctor_of_equivalence.{w, w'} e A B n
  exact ⟨fun h => @subsingleton_of_surjective _ _ _ hb.2 h,
    fun h => @subsingleton_of_injective _ _ _ hb.1 h⟩

end Vanishing

end Stacks.Homology

end
