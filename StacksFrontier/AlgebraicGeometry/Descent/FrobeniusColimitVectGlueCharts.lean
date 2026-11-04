module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueCover
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiHomGlueNested
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycleOfOverlapCharts

/-!
# Glueing finite locally free modules over the Frobenius colimit from free charts

Let `X` be a scheme in characteristic `p` and `V` an open cover of `X`.  Free modules of ranks
`m j` over the members, with isomorphisms `ψ j k` of the free modules over the overlaps satisfying
the cocycle condition over the triple overlaps, glue to a finite locally free `colim_F 𝒪_X`-module
whose restrictions to the members are the free modules, compatibly with the `ψ j k`.  This is the
object-glueing step of the Zariski glueing in the proof of [Stacks, Tag 0EXD].

The glueing itself is `Stacks.SheafOfModules.exists_glued_iso_over_of_overlap_of_eq`, which works
with slice restrictions `M.over V`; the data are given in the transition-functor spelling
`(V.ι)^* M`.  The passage between the two is `AlgebraicGeometry.frobeniusColimitVectHomEquivOver`,
and its compatibility with passing to a smaller open is
`AlgebraicGeometry.frobeniusColimitVectHomEquivOver_overMap`.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectHomEquivOver`: slice morphisms are morphisms of
  transitions, on the finite locally free modules.
* `AlgebraicGeometry.exists_frobeniusColimitVectorBundle_glue`: the glueing.

## Implementation notes

The slice restriction to `W ≤ V` of a morphism over `V` has a type which is only definitionally
the slice restriction over `W` of the two modules, and checking that definitional equality inside
an equation at the Frobenius colimit of the structure sheaf is expensive.  The restricted morphism
is therefore produced once, as an existential with its transition and its components
(`AlgebraicGeometry.exists_frobeniusColimitVectHomEquivOver_res_free`), and every later statement
is made about that witness.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The conjugation identity used for restricting a conjugate of a morphism of free modules,
in an arbitrary category: if `t ≫ a = P b ≫ c` at both ends then
`t⁻¹ ≫ P (b ≫ f ≫ b'⁻¹) ≫ t' = a ≫ (c⁻¹ ≫ P f ≫ c') ≫ a'⁻¹`. -/
private theorem conj_triangle' {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟)
    {B B' : 𝒞} {T T' A A' : 𝒟} {Q Q' : 𝒞}
    (b : B ≅ Q) (b' : B' ≅ Q') (t : P.obj B ≅ T) (t' : P.obj B' ≅ T')
    (a : T ≅ A) (a' : T' ≅ A') (c : P.obj Q ≅ A) (c' : P.obj Q' ≅ A')
    (h : t.hom ≫ a.hom = P.map b.hom ≫ c.hom) (h' : t'.hom ≫ a'.hom = P.map b'.hom ≫ c'.hom)
    (f : Q ⟶ Q') :
    t.inv ≫ P.map (b.hom ≫ f ≫ b'.inv) ≫ t'.hom = a.hom ≫ (c.inv ≫ P.map f ≫ c'.hom) ≫ a'.inv := by
  have ht : t.inv = a.hom ≫ c.inv ≫ P.map b.inv := by
    rw [← cancel_epi t.hom, Iso.hom_inv_id, reassoc_of% h, Iso.hom_inv_id_assoc, ← P.map_comp,
      Iso.hom_inv_id, P.map_id]
  have ht' : t'.hom = P.map b'.hom ≫ c'.hom ≫ a'.inv := by
    rw [← reassoc_of% h', Iso.hom_inv_id, Category.comp_id]
  have e1 : P.map b.inv ≫ P.map b.hom = 𝟙 _ := by rw [← P.map_comp, b.inv_hom_id, P.map_id]
  have e2 : P.map b'.inv ≫ P.map b'.hom = 𝟙 _ := by rw [← P.map_comp, b'.inv_hom_id, P.map_id]
  rw [ht, ht']
  simp only [Category.assoc, P.map_comp, reassoc_of% e1, reassoc_of% e2]

/-- Reassociation through a functor and a commuting square, in an arbitrary category. -/
private theorem comp_map_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ 𝒟)
    {A B C : 𝒞} {D E F : 𝒟} (a : D ⟶ P.obj A) (x : A ⟶ B) (y : B ⟶ C) (z : P.obj C ⟶ E)
    (t : P.obj B ⟶ F) (w : F ⟶ E) (h : t ≫ w = P.map y ≫ z) :
    a ≫ P.map (x ≫ y) ≫ z = (a ≫ P.map x ≫ t) ≫ w := by
  rw [P.map_comp, Category.assoc, Category.assoc, Category.assoc, h]

/-- Composing two conjugates through a common middle isomorphism, in an arbitrary category. -/
private theorem conj_comp_conj {𝒞 : Type*} [Category 𝒞] {A B C A' B' C' : 𝒞} (a : A ≅ A')
    (b : B ≅ B') (c : C ≅ C') (f : A' ⟶ B') (g : B' ⟶ C') :
    (a.hom ≫ f ≫ b.inv) ≫ (b.hom ≫ g ≫ c.inv) = a.hom ≫ f ≫ g ≫ c.inv := by
  simp

variable (p : ℕ) [Fact p.Prime] {X : Scheme.{u}} (hX : IsInCharacteristic X p)

local notation "F[" U ", " n "]" =>
  frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX U) n
local notation "FX[" n "]" => frobeniusColimitFreeVectorBundle p hX n

local notation "FI[" V ", " n "]" =>
  frobeniusColimitFreeVectorBundlePullbackIso p (Scheme.Opens.ι V)
    (isInCharacteristic_toScheme hX V) hX n
local notation "E[" V "]" =>
  frobeniusColimitPullbackHomEquivOver X p hX V (isInCharacteristic_toScheme hX V)

local notation "PV[" V "]" =>
  frobeniusColimitVectorBundlesPullback p (Scheme.Opens.ι V) (isInCharacteristic_toScheme hX V) hX

/-- `frobeniusColimitPullbackHomEquivOver` on the finite locally free modules. -/
noncomputable def frobeniusColimitVectHomEquivOver (V : X.Opens)
    (M N : frobeniusColimitVectorBundles X p hX) :
    (M.obj.over V ⟶ N.obj.over V) ≃ ((PV[V]).obj M ⟶ (PV[V]).obj N) where
  toFun f := ⟨E[V] M.obj N.obj f⟩
  invFun g := (E[V] M.obj N.obj).symm g.hom
  left_inv f := (E[V] M.obj N.obj).symm_apply_apply f
  right_inv g := ObjectProperty.hom_ext _ ((E[V] M.obj N.obj).apply_symm_apply g.hom)

/-- The underlying morphism of `frobeniusColimitVectHomEquivOver` is
`frobeniusColimitPullbackHomEquivOver` applied to the underlying modules. -/
theorem frobeniusColimitVectHomEquivOver_hom (V : X.Opens)
    {M N : frobeniusColimitVectorBundles X p hX}
    (f : M.obj.over V ⟶ N.obj.over V) :
    (frobeniusColimitVectHomEquivOver p hX V M N f).hom = E[V] M.obj N.obj f :=
  rfl

/-- `frobeniusColimitVectHomEquivOver` sends a composite of slice morphisms to the composite of
their images. -/
theorem frobeniusColimitVectHomEquivOver_comp (V : X.Opens)
    {M N K : frobeniusColimitVectorBundles X p hX} (f : M.obj.over V ⟶ N.obj.over V)
    (g : N.obj.over V ⟶ K.obj.over V) :
    frobeniusColimitVectHomEquivOver p hX V M K (f ≫ g) =
      frobeniusColimitVectHomEquivOver p hX V M N f ≫
        frobeniusColimitVectHomEquivOver p hX V N K g :=
  ObjectProperty.hom_ext _
    (frobeniusColimitPullbackHomEquivOver_comp X p hX V (isInCharacteristic_toScheme hX V) f g)

/-- `frobeniusColimitVectHomEquivOver` sends the identity slice morphism to the identity. -/
theorem frobeniusColimitVectHomEquivOver_id (V : X.Opens)
    (M : frobeniusColimitVectorBundles X p hX) :
    frobeniusColimitVectHomEquivOver p hX V M M (𝟙 _) = 𝟙 _ :=
  ObjectProperty.hom_ext _
    (frobeniusColimitPullbackHomEquivOver_id X p hX V (isInCharacteristic_toScheme hX V) M.obj)

/-- An isomorphism of slice restrictions as an isomorphism of transitions. -/
noncomputable def frobeniusColimitVectIsoOver (V : X.Opens)
    {M N : frobeniusColimitVectorBundles X p hX} (ν : M.obj.over V ≅ N.obj.over V) :
    (PV[V]).obj M ≅ (PV[V]).obj N where
  hom := frobeniusColimitVectHomEquivOver p hX V M N ν.hom
  inv := frobeniusColimitVectHomEquivOver p hX V N M ν.inv
  hom_inv_id := by
    rw [← frobeniusColimitVectHomEquivOver_comp, ν.hom_inv_id, frobeniusColimitVectHomEquivOver_id]
  inv_hom_id := by
    rw [← frobeniusColimitVectHomEquivOver_comp, ν.inv_hom_id, frobeniusColimitVectHomEquivOver_id]

/-- The inverse of an isomorphism in a full subcategory is the inverse of the underlying
isomorphism. -/
private theorem inv_hom_of_hom_hom {𝒞 : Type*} [Category 𝒞] (P : ObjectProperty 𝒞)
    {A B : P.FullSubcategory} (e : A ≅ B) (e' : A.obj ≅ B.obj) (h : e.hom.hom = e'.hom) :
    e.inv.hom = e'.inv :=
  congrArg Iso.inv ((Iso.ext h : (ObjectProperty.ι P).mapIso e = e'))

local notation "TR[" h "]" =>
  frobeniusColimitVectorBundlesPullbackTriangleIso p (Scheme.homOfLE _ h)
  (Scheme.Opens.ι _) (Scheme.Opens.ι _) (isInCharacteristic_toScheme hX _)
  (isInCharacteristic_toScheme hX _) hX (Scheme.homOfLE_ι _ h)
local notation "PH[" h "]" => frobeniusColimitVectorBundlesPullback p (Scheme.homOfLE _ h)
  (isInCharacteristic_toScheme hX _) (isInCharacteristic_toScheme hX _)

/-- The free identifications are compatible with the triangle comparison for `W ≤ V`. -/
private theorem free_triangle {V W : X.Opens} (h : W ≤ V) (n : ℕ) :
    (TR[h]).hom.app FX[n] ≫ FI[W, n].hom =
      (PH[h]).map FI[V, n].hom ≫
        (frobeniusColimitFreeVectorBundlePullbackIso p (X.homOfLE h)
          (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) n).hom :=
  frobeniusColimitFreeVectorBundlePullbackIso_triangle p (X.homOfLE h) V.ι W.ι
    (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) hX
    (Scheme.homOfLE_ι X h) n

/-- **The bijection with the transitions is compatible with passing to a smaller open.** -/
theorem frobeniusColimitVectHomEquivOver_overMap {V W : X.Opens} (h : W ≤ V)
    {M N : frobeniusColimitVectorBundles X p hX} (φ : M.obj.over V ⟶ N.obj.over V) :
    frobeniusColimitVectHomEquivOver p hX W M N
        ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map φ) =
      (TR[h]).inv.app M ≫ (PH[h]).map (frobeniusColimitVectHomEquivOver p hX V M N φ) ≫
        (TR[h]).hom.app N := by
  refine ObjectProperty.hom_ext _ ?_
  refine (frobeniusColimitPullbackHomEquivOver_overMap X p hX h (isInCharacteristic_toScheme hX V)
    (isInCharacteristic_toScheme hX W) φ).trans ?_
  have h₁ := frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom p (X.homOfLE h) V.ι W.ι
    (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) hX
    (Scheme.homOfLE_ι X h) N
  have h₂ := inv_hom_of_hom_hom _ ((TR[h]).app M)
    ((frobeniusColimitPullbackTriangleIso p (X.homOfLE h) V.ι W.ι
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) hX
      (Scheme.homOfLE_ι X h)).app M.obj)
    (frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom p (X.homOfLE h) V.ι W.ι
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) hX
      (Scheme.homOfLE_ι X h) M)
  exact (congrArg₂ (fun a c => a ≫ _ ≫ c) h₂ h₁).symm

/-- **The slice morphism attached to a morphism of free modules over `V` restricts, over
`W ≤ V`, to the slice morphism attached to its restriction.** -/
theorem frobeniusColimitVectHomEquivOver_overMap_free {V W : X.Opens} (h : W ≤ V) {n n' : ℕ}
    (f : F[V, n] ⟶ F[V, n']) (φ : (FX[n]).obj.over V ⟶ (FX[n']).obj.over V)
    (hφ : frobeniusColimitVectHomEquivOver p hX V FX[n] FX[n'] φ =
      FI[V, n].hom ≫ f ≫ FI[V, n'].inv) :
    frobeniusColimitVectHomEquivOver p hX W FX[n] FX[n']
        ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map φ) =
      FI[W, n].hom ≫ frobeniusColimitFreeRes p hX h f ≫ FI[W, n'].inv := by
  rw [frobeniusColimitVectHomEquivOver_overMap, hφ]
  exact conj_triangle' (PH[h]) FI[V, n] FI[V, n'] ((TR[h]).app _) ((TR[h]).app _)
    FI[W, n] FI[W, n']
    (frobeniusColimitFreeVectorBundlePullbackIso p (X.homOfLE h)
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) n)
    (frobeniusColimitFreeVectorBundlePullbackIso p (X.homOfLE h)
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) n')
    (free_triangle p hX h n) (free_triangle p hX h n') f

/-- **The restriction of a chart obtained from a slice trivialisation is obtained from the
restricted slice trivialisation.** -/
theorem frobeniusColimitResChart_isoOver {V W : X.Opens} (h : W ≤ V) {n : ℕ}
    {N : frobeniusColimitVectorBundles X p hX} (ν : N.obj.over V ≅ (FX[n]).obj.over V) :
    (frobeniusColimitResChart p hX h (frobeniusColimitVectIsoOver p hX V ν ≪≫ FI[V, n])).hom =
      frobeniusColimitVectHomEquivOver p hX W N FX[n]
          ((_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map
            ν.hom) ≫ FI[W, n].hom := by
  rw [frobeniusColimitVectHomEquivOver_overMap]
  exact comp_map_comp_eq (PH[h]) ((TR[h]).inv.app N) _ FI[V, n].hom _ ((TR[h]).hom.app FX[n])
    FI[W, n].hom
    (free_triangle p hX h n)

/-- **The restriction of a slice morphism to a smaller open, as a morphism over that open**,
together with its image under the bijection with the transitions and its components. -/
theorem exists_frobeniusColimitVectHomEquivOver_res {V W : X.Opens} (h : W ≤ V)
    {M N : frobeniusColimitVectorBundles X p hX} (φ : M.obj.over V ⟶ N.obj.over V) :
    ∃ g : M.obj.over W ⟶ N.obj.over W,
      frobeniusColimitVectHomEquivOver p hX W M N g =
        (TR[h]).inv.app M ≫ (PH[h]).map (frobeniusColimitVectHomEquivOver p hX V M N φ) ≫
          (TR[h]).hom.app N ∧
      ∀ ⦃W' : X.Opens⦄ (h₁ : W' ≤ W) (h₂ : W' ≤ V) (x : ToType (M.obj.val.obj (Opposite.op W'))),
        g.val.app (Opposite.op (Over.mk (homOfLE h₁))) x =
          φ.val.app (Opposite.op (Over.mk (homOfLE h₂))) x :=
  ⟨(_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map φ,
    frobeniusColimitVectHomEquivOver_overMap p hX h φ, fun _ _ _ _ => rfl⟩

/-- **The restriction of a slice morphism attached to a morphism of free modules, as a morphism
over the smaller open**: its transition is the restricted morphism of free modules, and its
components are those of the original morphism. -/
theorem exists_frobeniusColimitVectHomEquivOver_res_free {V W : X.Opens} (h : W ≤ V) {n n' : ℕ}
    (f : F[V, n] ⟶ F[V, n']) (φ : (FX[n]).obj.over V ⟶ (FX[n']).obj.over V)
    (hφ : frobeniusColimitVectHomEquivOver p hX V FX[n] FX[n'] φ =
      FI[V, n].hom ≫ f ≫ FI[V, n'].inv) :
    ∃ g : (FX[n]).obj.over W ⟶ (FX[n']).obj.over W,
      frobeniusColimitVectHomEquivOver p hX W FX[n] FX[n'] g =
        FI[W, n].hom ≫ frobeniusColimitFreeRes p hX h f ≫ FI[W, n'].inv ∧
      ∀ ⦃W' : X.Opens⦄ (h₁ : W' ≤ W) (h₂ : W' ≤ V)
        (x : ToType ((FX[n]).obj.val.obj (Opposite.op W'))),
        g.val.app (Opposite.op (Over.mk (homOfLE h₁))) x =
          φ.val.app (Opposite.op (Over.mk (homOfLE h₂))) x :=
  ⟨(_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX) (homOfLE h)).map φ,
    frobeniusColimitVectHomEquivOver_overMap_free p hX h f φ hφ, fun _ _ _ _ => rfl⟩

/-- **G1b: the charts read off slice trivialisations related by a slice comparison are related
by the corresponding morphism of free modules, after restriction to the overlap.** -/
theorem frobeniusColimitResChart_isoOver_compat {V₁ V₂ : X.Opens} {n₁ n₂ : ℕ}
    {N : frobeniusColimitVectorBundles X p hX}
    (ν₁ : N.obj.over V₁ ≅ (FX[n₁]).obj.over V₁) (ν₂ : N.obj.over V₂ ≅ (FX[n₂]).obj.over V₂)
    (φ : (FX[n₁]).obj.over (V₁ ⊓ V₂) ⟶ (FX[n₂]).obj.over (V₁ ⊓ V₂))
    (ψ : F[V₁ ⊓ V₂, n₁] ⟶ F[V₁ ⊓ V₂, n₂])
    (hφ : frobeniusColimitVectHomEquivOver p hX (V₁ ⊓ V₂) FX[n₁] FX[n₂] φ =
      FI[V₁ ⊓ V₂, n₁].hom ≫ ψ ≫ FI[V₁ ⊓ V₂, n₂].inv)
    (hν : ∀ ⦃W : X.Opens⦄ (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (h₁₂ : W ≤ V₁ ⊓ V₂),
      ν₂.hom.val.app (Opposite.op (Over.mk (homOfLE h₂))) =
        ν₁.hom.val.app (Opposite.op (Over.mk (homOfLE h₁))) ≫
          φ.val.app (Opposite.op (Over.mk (homOfLE h₁₂)))) :
    (frobeniusColimitResChart p hX (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
        (frobeniusColimitVectIsoOver p hX V₁ ν₁ ≪≫ FI[V₁, n₁])).hom ≫ ψ =
      (frobeniusColimitResChart p hX (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
        (frobeniusColimitVectIsoOver p hX V₂ ν₂ ≪≫ FI[V₂, n₂])).hom := by
  rw [frobeniusColimitResChart_isoOver, frobeniusColimitResChart_isoOver,
    frobeniusColimitVectHomEquivOver_overMap, frobeniusColimitVectHomEquivOver_overMap]
  obtain ⟨g₁, hg₁, hc₁⟩ := exists_frobeniusColimitVectHomEquivOver_res p hX
    (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ν₁.hom
  obtain ⟨g₂, hg₂, hc₂⟩ := exists_frobeniusColimitVectHomEquivOver_res p hX
    (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ν₂.hom
  rw [← hg₁, ← hg₂]
  have e : g₂ = g₁ ≫ φ := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    ext x
    have hU₁ : U.unop.left ≤ V₁ := (leOfHom U.unop.hom).trans inf_le_left
    have hU₂ : U.unop.left ≤ V₂ := (leOfHom U.unop.hom).trans inf_le_right
    refine (hc₂ (leOfHom U.unop.hom) hU₂ x).trans ?_
    refine (congrArg (fun t => t x) (congrArg ConcreteCategory.hom
      (hν hU₁ hU₂ (leOfHom U.unop.hom)))).trans ?_
    exact congrArg ((φ.val.app U).hom) (hc₁ (leOfHom U.unop.hom) hU₁ x).symm
  rw [e, frobeniusColimitVectHomEquivOver_comp, hφ]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **G1: free charts over an open cover with comparisons over the pairwise intersections
satisfying the cocycle condition glue to a finite locally free module whose restrictions to the
members are the charts, compatibly with the comparisons.**

The comparisons are read as morphisms of slice restrictions of free modules over `X`
(`AlgebraicGeometry.frobeniusColimitVectHomEquivOver` and the free identifications), the cocycle
condition then holds componentwise on the slices
(`AlgebraicGeometry.frobeniusColimitVectHomEquivOver_overMap_free`), and the glueing with recorded
charts is `Stacks.SheafOfModules.exists_glued_iso_over_of_overlap_of_eq`; its charts are read back
as isomorphisms of transitions. -/
theorem exists_frobeniusColimitVectorBundle_glue {J : Type u} (V : J → X.Opens)
    (hV : ⨆ j, V j = ⊤) (m : J → ℕ)
    (ψ : ∀ j k, frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX (V j ⊓ V k))
        (m j) ≅ frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX (V j ⊓ V k))
        (m k))
    (hid : ∀ j, (ψ j j).hom = 𝟙 _)
    (hcocycle : ∀ j k l,
      (frobeniusColimitFreeResIso p hX (inf_le_left : V j ⊓ V k ⊓ V l ≤ V j ⊓ V k) (ψ j k)).hom ≫
        (frobeniusColimitFreeResIso p hX
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            V j ⊓ V k ⊓ V l ≤ V k ⊓ V l) (ψ k l)).hom =
      (frobeniusColimitFreeResIso p hX
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            V j ⊓ V k ⊓ V l ≤ V j ⊓ V l) (ψ j l)).hom) :
    ∃ (N : frobeniusColimitVectorBundles X p hX)
      (c : ∀ j, (frobeniusColimitVectorBundlesPullback p (V j).ι
          (isInCharacteristic_toScheme hX (V j)) hX).obj N ≅
        frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX (V j)) (m j)),
      ∀ j k, (frobeniusColimitResChart p hX (inf_le_left : V j ⊓ V k ≤ V j) (c j)).hom ≫
          (ψ j k).hom =
        (frobeniusColimitResChart p hX (inf_le_right : V j ⊓ V k ≤ V k) (c k)).hom := by
  let R := frobeniusColimitRingSheaf X p hX
  obtain ⟨φ, hφ⟩ : ∃ φ : ∀ j k, (FX[m j]).obj.over (V j ⊓ V k) ⟶ (FX[m k]).obj.over (V j ⊓ V k),
      ∀ j k, frobeniusColimitVectHomEquivOver p hX (V j ⊓ V k) FX[m j] FX[m k] (φ j k) =
        FI[V j ⊓ V k, m j].hom ≫ (ψ j k).hom ≫ FI[V j ⊓ V k, m k].inv :=
    ⟨fun j k => (frobeniusColimitVectHomEquivOver p hX (V j ⊓ V k) FX[m j] FX[m k]).symm
        (FI[V j ⊓ V k, m j].hom ≫ (ψ j k).hom ≫ FI[V j ⊓ V k, m k].inv),
      fun j k => Equiv.apply_symm_apply _ _⟩
  have hφid : ∀ j, φ j j = 𝟙 _ := fun j => by
    refine (frobeniusColimitVectHomEquivOver p hX (V j ⊓ V j) FX[m j] FX[m j]).injective ?_
    rw [hφ, hid, Category.id_comp, Iso.hom_inv_id, frobeniusColimitVectHomEquivOver_id]
  have hcomp : ∀ (k l j : J) ⦃W : X.Opens⦄ (hkl : W ≤ V k ⊓ V l) (hlj : W ≤ V l ⊓ V j)
      (hkj : W ≤ V k ⊓ V j) (x : ToType ((FX[m k]).obj.val.obj (op W))),
      (φ l j).val.app (op (Over.mk (homOfLE hlj)))
          ((φ k l).val.app (op (Over.mk (homOfLE hkl))) x)
        = (φ k j).val.app (op (Over.mk (homOfLE hkj))) x := by
    intro k l j W hkl hlj hkj x
    have hW : W ≤ V k ⊓ V l ⊓ V j := le_inf hkl (hlj.trans inf_le_right)
    obtain ⟨g₁, hg₁, hc₁⟩ := exists_frobeniusColimitVectHomEquivOver_res_free p hX
      (inf_le_left : V k ⊓ V l ⊓ V j ≤ V k ⊓ V l) (ψ k l).hom (φ k l) (hφ k l)
    obtain ⟨g₂, hg₂, hc₂⟩ := exists_frobeniusColimitVectHomEquivOver_res_free p hX
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V k ⊓ V l ⊓ V j ≤ V l ⊓ V j)
      (ψ l j).hom (φ l j) (hφ l j)
    obtain ⟨g₃, hg₃, hc₃⟩ := exists_frobeniusColimitVectHomEquivOver_res_free p hX
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V k ⊓ V l ⊓ V j ≤ V k ⊓ V j)
      (ψ k j).hom (φ k j) (hφ k j)
    have e : g₁ ≫ g₂ = g₃ := by
      refine (frobeniusColimitVectHomEquivOver p hX (V k ⊓ V l ⊓ V j) FX[m k] FX[m j]).injective ?_
      rw [frobeniusColimitVectHomEquivOver_comp, hg₁, hg₂, hg₃]
      refine (conj_comp_conj _ _ _ _ _).trans ?_
      have hc := hcocycle k l j
      simp only [frobeniusColimitFreeResIso] at hc
      exact congrArg (fun t => FI[V k ⊓ V l ⊓ V j, m k].hom ≫ t ≫
        FI[V k ⊓ V l ⊓ V j, m j].inv) hc
    refine (congrArg ((φ l j).val.app (op (Over.mk (homOfLE hlj)))).hom
      (hc₁ hW hkl x).symm).trans ?_
    refine (hc₂ hW hlj _).symm.trans ?_
    refine (congrArg (fun t => t.val.app (op (Over.mk (homOfLE hW))) x) e).trans ?_
    exact hc₃ hW hkj x
  have hid' : ∀ (k : J) ⦃W : X.Opens⦄ (hk : W ≤ V k ⊓ V k)
      (x : ToType ((FX[m k]).obj.val.obj (op W))),
      (φ k k).val.app (op (Over.mk (homOfLE hk))) x = x := fun k W hk x => by
    rw [hφid k]; rfl
  obtain ⟨N₀, ν, hN₀, hν⟩ := Stacks.SheafOfModules.exists_glued_iso_over_of_overlap_of_eq
    (O := R) V hV m (fun k l => V k ⊓ V l) (fun _ _ => rfl) φ hid' hcomp
  let N : frobeniusColimitVectorBundles X p hX := ⟨N₀, hN₀⟩
  refine ⟨N, fun j => frobeniusColimitVectIsoOver p hX (V j) (N := FX[m j]) (M := N) (ν j) ≪≫
    FI[V j, m j], fun j k => ?_⟩
  exact frobeniusColimitResChart_isoOver_compat p hX (N := N) (ν j) (ν k) (φ j k) (ψ j k).hom
    (hφ j k) (fun W h₁ h₂ h₁₂ => hν j k h₁ h₂ h₁₂)

end AlgebraicGeometry

end
