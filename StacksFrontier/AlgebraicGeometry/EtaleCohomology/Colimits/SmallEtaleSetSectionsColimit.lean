module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageDegreeZeroSetColimit
public import StacksFrontier.CategoryTheory.Sites.FreeAbelianSheafUnit

/-!
# Stacks 09YQ in degree zero for sheaves of sets, over a quasi-compact quasi-separated object

Let `(X_i)` be an inverse system of schemes over a nonempty directed set with affine transition
morphisms and `X = lim X_i`, let `(F_i)` be a system of sheaves of **sets** on the `X_i` in the
sense of [Stacks, Tag 0EZL] and `𝓕 = colim f_i^{-1}F_i` on `X`, the colimit presented by its
universal property in adjoint form. This file proves that for every étale `X_{i₀}`-scheme `W`
which is quasi-compact and quasi-separated, the sections of `𝓕` over the base change of `W` to
`X` are the filtered colimit of the sections of the `F_i` over the base changes of `W` to the
`X_i` (`Stacks.EtaleCohomology.SetLinearization.isSectionsColimitAt_of_presentation`). This is
[Stacks, Tag 09YQ] in degree zero over `W`, for sheaves of sets.

The tree carries this statement for abelian sheaves
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.qcqsSections_isColimit`), and the proof here
reduces to it through the free abelian sheaf `ℤ[-]`, left adjoint to the underlying sheaf of sets
`U`:

* `ℤ[-]` carries a presented system of sheaves of sets to a presented system of abelian sheaves
  (`Stacks.EtaleCohomology.SetLinearization.isDirPresentation_free`): the universal property of
  `ℤ[𝓕] = colim f_i^{-1}ℤ[F_i]` is that of `𝓕` read through the adjunction;
* for a presented system of abelian sheaves the sections colimit holds on the underlying sheaves
  of sets (`Stacks.EtaleCohomology.SetLinearization.isSectionsColimitAt_forget`), and so, by the
  degree-zero argument of [Stacks, Tag 0EYM] with `g` the identity
  (`Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_desc_of_sectionsColimit`), the
  underlying system of sheaves of sets is again presented
  (`Stacks.EtaleCohomology.SetLinearization.isDirPresentation_forget`);
* a sheaf of sets `G` is the equalizer of the two maps `η_{Uℤ[G]}`, `Uℤ[η_G]` from `Uℤ[G]` to
  `Uℤ[Uℤ[G]]`, and `η_G` is injective (`Stacks.FreeAbelianSheaf.exists_unit_eq_of_unit_eq`,
  `Stacks.FreeAbelianSheaf.unit_injective`); filtered colimits of sets commute with equalizers,
  so the sections colimit for `F` follows from the sections colimits for `Uℤ[F]` and
  `Uℤ[Uℤ[F]]`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.ofMapTranspose` — a system of sheaves from its
  transposed transition maps and their cocycle law.
* `Stacks.EtaleCohomology.SetLinearization.IsDirPresentation` — the universal property of
  `𝓕 = colim f_i^{-1}F_i` in adjoint form.
* `Stacks.EtaleCohomology.SetLinearization.freeSystem`,
  `Stacks.EtaleCohomology.SetLinearization.forgetSystem` — the systems `ℤ[F_i]` and `U(A_i)`.

## Main results

* `Stacks.EtaleCohomology.SetLinearization.isSectionsColimitAt_of_presentation` — **[Stacks,
  Tag 09YQ] in degree zero for sheaves of sets, over a quasi-compact quasi-separated étale object
  of a stage.**

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology Stacks.EtaleCohomology.LimitDirectImage

universe w' w v u

namespace Stacks.EtaleCohomology

/-! ### A system of sheaves from its transposed transition maps -/

section OfMapTranspose

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {A : Type w} [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- **A system of sheaves from its transposed transition maps.** Maps `t_a : G_j ⟶ f_{a, *}G_i`
satisfying the transposed cocycle law are the transposes of the transition maps of a unique system
of sheaves in the sense of [Stacks, Tag 0EZL]. -/
abbrev EtaleSheafSystem.ofMapTranspose (G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A)
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G j ⟶ (systemPushforward D A a).obj (G i))
    (ht : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
      t (a ≫ b) = t b ≫ (systemPushforward D A b).map (t a) ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          A).hom.app (G i)) :
    EtaleSheafSystem D A where
  obj := G
  map a := ((systemAdjunction D A a).homEquiv _ _).symm (t a)
  map_comp {i j k} a b := by
    refine (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A b)
      (systemAdjunction D A a) (systemAdjunction D A (a ≫ b))
      (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) A)
      _ _).trans ?_
    exact congrArg ((systemAdjunction D A (a ≫ b)).homEquiv _ _).symm (ht a b).symm

/-- The transposed transition maps of `EtaleSheafSystem.ofMapTranspose G t ht` are the maps `t`. -/
theorem EtaleSheafSystem.mapTranspose_ofMapTranspose
    (G : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A)
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G j ⟶ (systemPushforward D A a).obj (G i))
    (ht : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
      t (a ≫ b) = t b ≫ (systemPushforward D A b).map (t a) ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          A).hom.app (G i)) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (EtaleSheafSystem.ofMapTranspose G t ht).mapTranspose a = t a :=
  Equiv.apply_symm_apply _ _

end OfMapTranspose

namespace SetLinearization

/-! ### Maps of systems and the shifted maps -/

section Shift

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {A : Type w} [Category.{w'} A]
  {c : Cone D}

/-- **A map of families commuting with the legs commutes with the shifted legs.** -/
theorem map_comp_shiftLeg {G G' : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    {Y Y' : Sheaf (smallEtaleTopology c.pt) A}
    (x : ∀ i : Iᵒᵖ, G i ⟶ (smallEtalePushforward (c.π.app i) A).obj Y)
    (x' : ∀ i : Iᵒᵖ, G' i ⟶ (smallEtalePushforward (c.π.app i) A).obj Y')
    (φ : ∀ i : Iᵒᵖ, G i ⟶ G' i) (ψ : Y ⟶ Y')
    (hφ : ∀ i : Iᵒᵖ, φ i ≫ x' i = x i ≫ (smallEtalePushforward (c.π.app i) A).map ψ)
    {k j : Iᵒᵖ} (a : k ⟶ j) :
    (systemPushforward D A a).map (φ k) ≫ shiftLeg (c := c) x' a =
      shiftLeg (c := c) x a ≫ (smallEtalePushforward (c.π.app j) A).map ψ := by
  have hn := (coneProjectionComp A c a).hom.naturality ψ
  dsimp only [Functor.comp_map] at hn
  simp only [shiftLeg]
  rw [← Category.assoc, ← Functor.map_comp, hφ k, Functor.map_comp, Category.assoc, hn,
    Category.assoc]

/-- **A map of families commuting with the transposed transitions commutes with the shifted
transition maps.** -/
theorem map_comp_shiftTransition {G G' : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A}
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G j ⟶ (systemPushforward D A a).obj (G i))
    (t' : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), G' j ⟶ (systemPushforward D A a).obj (G' i))
    (φ : ∀ i : Iᵒᵖ, G i ⟶ G' i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), φ j ≫ t' a = t a ≫ (systemPushforward D A a).map (φ i))
    {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a) :
    (systemPushforward D A a).map (φ k) ≫ shiftTransition A t' b a ab hab =
      shiftTransition A t b a ab hab ≫ (systemPushforward D A ab).map (φ l) := by
  have hn := (smallEtalePushforwardComp' (D.map b) (D.map a) (D.map ab)
    (by rw [hab, D.map_comp]) A).hom.naturality (φ l)
  dsimp only [Functor.comp_map] at hn
  simp only [shiftTransition]
  rw [← Category.assoc, ← Functor.map_comp, hφ b, Functor.map_comp, Category.assoc, hn,
    Category.assoc]

end Shift

/-! ### The universal property of a presentation, in adjoint form -/

section Presentation

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] (c : Cone D)

/-- The compatibility of a family of maps `τ_i : F_i ⟶ f_{i, *}𝒦` with the transposed transition
maps of a system. -/
def IsDirCompatible (F : EtaleSheafSystem D A) (𝒦 : Sheaf (smallEtaleTopology c.pt) A)
    (τ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) A).obj 𝒦) : Prop :=
  ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
    τ j = F.mapTranspose a ≫ (systemPushforward D A a).map (τ i) ≫
      (coneProjectionComp A c a).hom.app 𝒦

/-- **`𝓕 = colim f_i^{-1}F_i`, in adjoint form**: the maps `x_i : F_i ⟶ f_{i, *}𝓕` are
compatible with the transitions, and every compatible family `τ_i : F_i ⟶ f_{i, *}𝒦` is `x_i`
followed by `f_{i, *}χ` for a unique `χ : 𝓕 ⟶ 𝒦`. -/
def IsDirPresentation (F : EtaleSheafSystem D A) (𝓕 : Sheaf (smallEtaleTopology c.pt) A)
    (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) A).obj 𝓕) : Prop :=
  IsDirCompatible A c F 𝓕 x ∧
    ∀ (𝒦 : Sheaf (smallEtaleTopology c.pt) A)
      (τ : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) A).obj 𝒦),
      IsDirCompatible A c F 𝒦 τ →
        ∃! χ : 𝓕 ⟶ 𝒦, ∀ i : Iᵒᵖ, x i ≫ (smallEtalePushforward (c.π.app i) A).map χ = τ i

/-- A compatible family stays compatible after a map of the target. -/
theorem IsDirCompatible.comp_map {F : EtaleSheafSystem D A}
    {𝓕 𝒦 : Sheaf (smallEtaleTopology c.pt) A}
    {x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) A).obj 𝓕}
    (hx : IsDirCompatible A c F 𝓕 x) (ψ : 𝓕 ⟶ 𝒦) :
    IsDirCompatible A c F 𝒦 (fun i => x i ≫ (smallEtalePushforward (c.π.app i) A).map ψ) := by
  intro i j a
  have hn := (coneProjectionComp A c a).hom.naturality ψ
  dsimp only [Functor.comp_map] at hn
  dsimp only
  rw [hx a, Functor.map_comp]
  simp only [Category.assoc, hn]

end Presentation

/-! ### The free abelian sheaf and the underlying sheaf of sets -/

section Free

/-- The free abelian sheaf on a sheaf of sets on the small étale site. -/
abbrev freeAb (X : Scheme.{u}) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  FreeAbelianSheaf.freeSheaf (smallEtaleTopology X)

/-- The underlying sheaf of sets of an abelian sheaf on the small étale site. -/
abbrev forgetAb (X : Scheme.{u}) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  FreeAbelianSheaf.forgetSheaf (smallEtaleTopology X)

/-- The adjunction `ℤ[-] ⊣ U` on the small étale site. -/
abbrev freeAdj (X : Scheme.{u}) : freeAb X ⊣ forgetAb X :=
  FreeAbelianSheaf.freeSheafAdj (smallEtaleTopology X)

/-- **The underlying sheaf of sets commutes with direct image, on the nose.** -/
theorem forgetAb_map_pushforward_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : M ⟶ N) :
    (forgetAb Y).map ((smallEtalePushforward f AddCommGrpCat.{u + 1}).map φ) =
      (smallEtalePushforward f (Type (u + 1))).map ((forgetAb X).map φ) :=
  rfl

/-- **The underlying sheaf of sets commutes with the comparison of direct images along a
composite.** -/
theorem forgetAb_map_pushforwardComp'_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (M : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (forgetAb Z).map ((smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app M) =
      (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app ((forgetAb X).obj M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  ext s
  change ((smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app M).hom.app U s =
    ((smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app ((forgetAb X).obj M)).hom.app
      U s
  rw [show ((smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app M).hom.app U =
      M.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) from
    Category.id_comp _,
    show ((smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app
        ((forgetAb X).obj M)).hom.app U =
      ((forgetAb X).obj M).obj.map
        (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) from
    Category.id_comp _]
  rfl

/-- The underlying sheaf of sets of a direct image followed by a comparison of direct images. -/
private theorem forgetAb_map_pushforward_map_comp_pushforwardComp'_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    {M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}}
    {N : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}}
    (n : M ⟶ (smallEtalePushforward f AddCommGrpCat.{u + 1}).obj N) :
    (forgetAb Z).map ((smallEtalePushforward g AddCommGrpCat.{u + 1}).map n ≫
        (smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app N) =
      (smallEtalePushforward g (Type (u + 1))).map ((forgetAb Y).map n) ≫
        (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app ((forgetAb X).obj N) := by
  rw [Functor.map_comp, forgetAb_map_pushforward_map, forgetAb_map_pushforwardComp'_hom_app]
  rfl

/-- The unit followed by the underlying map is the transpose. -/
theorem unit_comp_forgetAb_map {X : Scheme.{u}} {P : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    {M : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (m : (freeAb X).obj P ⟶ M) :
    (freeAdj X).unit.app P ≫ (forgetAb X).map m = (freeAdj X).homEquiv _ _ m :=
  (Adjunction.homEquiv_unit _ _ _ m).symm

/-- The unit followed by the underlying map is the transpose, after applying a functor. -/
private theorem map_unit_comp_map_forgetAb_map {X : Scheme.{u}}
    {P : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    {M : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} {𝒟 : Type*} [Category* 𝒟]
    (G : Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ 𝒟) (m : (freeAb X).obj P ⟶ M) :
    G.map ((freeAdj X).unit.app P) ≫ G.map ((forgetAb X).map m) =
      G.map ((freeAdj X).homEquiv _ _ m) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg G.map (unit_comp_forgetAb_map m))

/-- **The transpose of a map followed by a direct image and a comparison of direct images.** -/
theorem homEquiv_comp_pushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) {P : Sheaf (smallEtaleTopology Z) (Type (u + 1))}
    {M : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}}
    {N : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}}
    (m : (freeAb Z).obj P ⟶ (smallEtalePushforward g AddCommGrpCat.{u + 1}).obj M)
    (n : M ⟶ (smallEtalePushforward f AddCommGrpCat.{u + 1}).obj N) :
    (freeAdj Z).homEquiv _ _ (m ≫ (smallEtalePushforward g AddCommGrpCat.{u + 1}).map n ≫
        (smallEtalePushforwardComp' f g fg hfg AddCommGrpCat.{u + 1}).hom.app N) =
      (freeAdj Z).homEquiv _ _ m ≫
        (smallEtalePushforward g (Type (u + 1))).map ((forgetAb Y).map n) ≫
          (smallEtalePushforwardComp' f g fg hfg (Type (u + 1))).hom.app ((forgetAb X).obj N) := by
  rw [Adjunction.homEquiv_naturality_right, Functor.map_comp, forgetAb_map_pushforward_map,
    forgetAb_map_pushforwardComp'_hom_app]
  rfl

end Free

/-! ### The free abelian system on a system of sheaves of sets -/

/-- Substituting a factorisation and contracting, in an arbitrary category. -/
theorem comp_eq_of_eq_comp {𝒜 : Type*} [Category* 𝒜] {X₀ X₁ X₂ X₃ : 𝒜}
    {m : X₀ ⟶ X₂} {f : X₀ ⟶ X₁} {p : X₁ ⟶ X₂} {q : X₂ ⟶ X₃} {r : X₁ ⟶ X₃}
    (e₁ : m = f ≫ p) (e₂ : p ≫ q = r) : m ≫ q = f ≫ r := by
  rw [e₁, Category.assoc, e₂]

/-- Moving a square past a further map, in an arbitrary category. -/
theorem comp_comp_eq_of_square {𝒜 : Type*} [Category* 𝒜] {X₀ X₁ X₂ X₃ X₄ : 𝒜}
    {e : X₀ ⟶ X₁} {m : X₁ ⟶ X₂} {n : X₂ ⟶ X₃} {f : X₀ ⟶ X₄} {p : X₄ ⟶ X₂} {r : X₄ ⟶ X₃}
    (h₁ : e ≫ m = f ≫ p) (h₂ : p ≫ n = r) : e ≫ m ≫ n = f ≫ r := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- `Stacks.EtaleCohomology.SetLinearization.comp_eq_of_eq_comp` followed by a further map. -/
theorem comp_comp_eq_of_eq_comp {𝒜 : Type*} [Category* 𝒜] {X₀ X₁ X₂ X₃ X₄ : 𝒜}
    {m : X₀ ⟶ X₂} {f : X₀ ⟶ X₁} {p : X₁ ⟶ X₂} {q : X₂ ⟶ X₃} {r : X₁ ⟶ X₃} {c : X₃ ⟶ X₄}
    (e₁ : m = f ≫ p) (e₂ : p ≫ q = r) : m ≫ q ≫ c = f ≫ r ≫ c := by
  rw [e₁, Category.assoc, ← Category.assoc p, e₂]

/-- The rearrangement behind `Stacks.EtaleCohomology.SetLinearization.freeTransition_comp`, in an
arbitrary category. -/
theorem comp_comp_algebra {𝒜 : Type*} [Category* 𝒜] {X₀ X₁ X₂ X₃ X₄ P Q : 𝒜}
    {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {h : X₃ ⟶ X₄} {p : X₁ ⟶ P} {q : P ⟶ Q}
    {r : X₂ ⟶ Q} {c' : Q ⟶ X₄} (h₁ : p ≫ q = g ≫ r) (h₂ : r ≫ c' = c ≫ h) :
    (f ≫ g ≫ c) ≫ h = (f ≫ p) ≫ q ≫ c' := by
  simp only [Category.assoc, reassoc_of% h₁, h₂]

section FreeSystem

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  (F : EtaleSheafSystem D (Type (u + 1)))

/-- The transposed transition map of the free abelian system: the transpose under `ℤ[-] ⊣ U` of
the transposed transition map of `F` followed by the direct image of the unit. -/
def freeTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeAb (D.obj j)).obj (F.obj j) ⟶
      (systemPushforward D AddCommGrpCat.{u + 1} a).obj ((freeAb (D.obj i)).obj (F.obj i)) :=
  ((freeAdj (D.obj j)).homEquiv _ _).symm
    (F.mapTranspose a ≫ (systemPushforward D (Type (u + 1)) a).map
      ((freeAdj (D.obj i)).unit.app (F.obj i)))

/-- The transpose of `freeTransition F a` under `ℤ[-] ⊣ U` is the transposed transition map of `F`
followed by the direct image of the unit. -/
theorem homEquiv_freeTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeAdj (D.obj j)).homEquiv _ _ (freeTransition F a) =
      F.mapTranspose a ≫ (systemPushforward D (Type (u + 1)) a).map
        ((freeAdj (D.obj i)).unit.app (F.obj i)) :=
  Equiv.apply_symm_apply _ _

/-- The cocycle law of `Stacks.EtaleCohomology.SetLinearization.freeTransition`. -/
theorem freeTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    freeTransition F (a ≫ b) = freeTransition F b ≫
      (systemPushforward D AddCommGrpCat.{u + 1} b).map (freeTransition F a) ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          AddCommGrpCat.{u + 1}).hom.app ((freeAb (D.obj i)).obj (F.obj i)) := by
  apply ((freeAdj (D.obj k)).homEquiv _ _).injective
  rw [homEquiv_comp_pushforward_comp, homEquiv_freeTransition, homEquiv_freeTransition,
    F.mapTranspose_comp]
  have hn := (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
    (Type (u + 1))).hom.naturality ((freeAdj (D.obj i)).unit.app (F.obj i))
  dsimp only [Functor.comp_map] at hn
  have h₁ : (systemPushforward D (Type (u + 1)) b).map ((freeAdj (D.obj j)).unit.app (F.obj j)) ≫
      (systemPushforward D (Type (u + 1)) b).map ((forgetAb (D.obj j)).map (freeTransition F a)) =
      (systemPushforward D (Type (u + 1)) b).map (F.mapTranspose a) ≫
        (systemPushforward D (Type (u + 1)) b).map ((systemPushforward D (Type (u + 1)) a).map
          ((freeAdj (D.obj i)).unit.app (F.obj i))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, unit_comp_forgetAb_map, homEquiv_freeTransition]
    rfl
  exact comp_comp_algebra h₁ hn

/-- **The free abelian system** `i ↦ ℤ[F_i]` on a system of sheaves of sets. -/
abbrev freeSystem : EtaleSheafSystem D AddCommGrpCat.{u + 1} :=
  EtaleSheafSystem.ofMapTranspose (fun i => (freeAb (D.obj i)).obj (F.obj i))
    (fun a => freeTransition F a) (fun a b => freeTransition_comp F a b)

/-- The transposed transition maps of `freeSystem F` are the maps `freeTransition F`. -/
theorem freeSystem_mapTranspose {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeSystem F).mapTranspose a = freeTransition F a :=
  EtaleSheafSystem.mapTranspose_ofMapTranspose _ _ _ a

end FreeSystem

/-! ### The free abelian system on a presented system of sheaves of sets -/

section FreePresentation

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
  (F : EtaleSheafSystem D (Type (u + 1)))
  {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (u + 1))).obj 𝓕)

/-- The legs `ℤ[F_i] ⟶ f_{i, *}ℤ[𝓕]` of the free abelian system: the transposes of `x_i`
followed by the direct image of the unit. -/
def freeLeg (i : Iᵒᵖ) :
    (freeAb (D.obj i)).obj (F.obj i) ⟶
      (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj ((freeAb c.pt).obj 𝓕) :=
  ((freeAdj (D.obj i)).homEquiv _ _).symm
    (x i ≫ (smallEtalePushforward (c.π.app i) (Type (u + 1))).map ((freeAdj c.pt).unit.app 𝓕))

/-- The transpose of `freeLeg F x i` under `ℤ[-] ⊣ U` is `x i` followed by the direct image of the
unit. -/
theorem homEquiv_freeLeg (i : Iᵒᵖ) :
    (freeAdj (D.obj i)).homEquiv _ _ (freeLeg F x i) =
      x i ≫ (smallEtalePushforward (c.π.app i) (Type (u + 1))).map ((freeAdj c.pt).unit.app 𝓕) :=
  Equiv.apply_symm_apply _ _

/-- The transpose of the compatibility condition of the free abelian system. -/
theorem homEquiv_freeTransition_comp {𝒞 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (τ : ∀ i : Iᵒᵖ, (freeSystem F).obj i ⟶
      (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒞) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeAdj (D.obj j)).homEquiv _ _ ((freeSystem F).mapTranspose a ≫
        (systemPushforward D AddCommGrpCat.{u + 1} a).map (τ i) ≫
          (coneProjectionComp AddCommGrpCat.{u + 1} c a).hom.app 𝒞) =
      F.mapTranspose a ≫ (systemPushforward D (Type (u + 1)) a).map
          ((freeAdj (D.obj i)).homEquiv _ _ (τ i)) ≫
        (coneProjectionComp (Type (u + 1)) c a).hom.app ((forgetAb c.pt).obj 𝒞) := by
  rw [freeSystem_mapTranspose]
  have h₀ := homEquiv_comp_pushforward_comp (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm
    (freeTransition F a) (τ i)
  exact h₀.trans (comp_comp_eq_of_eq_comp (homEquiv_freeTransition F a)
    (map_unit_comp_map_forgetAb_map (systemPushforward D (Type (u + 1)) a) (τ i)))

/-- **The compatibility of a family out of the free abelian system is the compatibility of the
transposed family.** -/
theorem isDirCompatible_free_iff {𝒞 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (τ : ∀ i : Iᵒᵖ, (freeSystem F).obj i ⟶
      (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒞) :
    IsDirCompatible AddCommGrpCat.{u + 1} c (freeSystem F) 𝒞 τ ↔
      IsDirCompatible (Type (u + 1)) c F ((forgetAb c.pt).obj 𝒞)
        (fun i => (freeAdj (D.obj i)).homEquiv _ _ (τ i)) := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun a => ?_
  have h := homEquiv_freeTransition_comp F τ a
  exact ⟨fun e => (congrArg ((freeAdj (D.obj j)).homEquiv _ _) e).trans h,
    fun e => ((freeAdj (D.obj j)).homEquiv _ _).injective (e.trans h.symm)⟩

/-- The transpose of a leg followed by the direct image of a map out of `ℤ[𝓕]`. -/
theorem homEquiv_freeLeg_comp {𝒞 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (χ : (freeAb c.pt).obj 𝓕 ⟶ 𝒞) (i : Iᵒᵖ) :
    (freeAdj (D.obj i)).homEquiv _ _
        (freeLeg F x i ≫ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).map χ) =
      x i ≫ (smallEtalePushforward (c.π.app i) (Type (u + 1))).map
        ((freeAdj c.pt).homEquiv _ _ χ) := by
  have h₀ : (freeAdj (D.obj i)).homEquiv _ _
        (freeLeg F x i ≫ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).map χ) =
      (freeAdj (D.obj i)).homEquiv _ _ (freeLeg F x i) ≫
        (forgetAb (D.obj i)).map
          ((smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).map χ) :=
    Adjunction.homEquiv_naturality_right _ _ _
  exact h₀.trans (comp_eq_of_eq_comp (homEquiv_freeLeg F x i)
    (map_unit_comp_map_forgetAb_map (smallEtalePushforward (c.π.app i) (Type (u + 1))) χ))

/-- **The free abelian system on a presented system of sheaves of sets is presented**:
`ℤ[𝓕] = colim f_i^{-1}ℤ[F_i]`, the universal property being that of `𝓕` read through the
adjunction `ℤ[-] ⊣ U`. -/
theorem isDirPresentation_free (h : IsDirPresentation (Type (u + 1)) c F 𝓕 x) :
    IsDirPresentation AddCommGrpCat.{u + 1} c (freeSystem F) ((freeAb c.pt).obj 𝓕)
      (freeLeg F x) := by
  refine ⟨(isDirCompatible_free_iff F (freeLeg F x)).mpr fun i j a => ?_, fun 𝒞 τ hτ => ?_⟩
  · exact (homEquiv_freeLeg F x j).trans
      ((IsDirCompatible.comp_map (Type (u + 1)) c h.1 ((freeAdj c.pt).unit.app 𝓕) a).trans
        (congrArg (fun z => F.mapTranspose a ≫ (systemPushforward D (Type (u + 1)) a).map z ≫
          (coneProjectionComp (Type (u + 1)) c a).hom.app ((forgetAb c.pt).obj
            ((freeAb c.pt).obj 𝓕))) (homEquiv_freeLeg F x i).symm))
  · obtain ⟨χ, hχ, hu⟩ := h.2 ((forgetAb c.pt).obj 𝒞) _ ((isDirCompatible_free_iff F τ).mp hτ)
    refine ⟨((freeAdj c.pt).homEquiv _ _).symm χ, fun i => ?_, fun χ' hχ' => ?_⟩
    · apply ((freeAdj (D.obj i)).homEquiv _ _).injective
      rw [homEquiv_freeLeg_comp, Equiv.apply_symm_apply, hχ i]
    · apply ((freeAdj c.pt).homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      refine hu _ fun i => ?_
      rw [← homEquiv_freeLeg_comp, hχ' i]

end FreePresentation

/-! ### The underlying system of sheaves of sets of an abelian system -/

section ForgetSystem

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  (FA : EtaleSheafSystem D AddCommGrpCat.{u + 1})

/-- The cocycle law of the underlying transposed transition maps. -/
theorem forgetTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (forgetAb (D.obj k)).map (FA.mapTranspose (a ≫ b)) =
      (forgetAb (D.obj k)).map (FA.mapTranspose b) ≫
        (systemPushforward D (Type (u + 1)) b).map ((forgetAb (D.obj j)).map (FA.mapTranspose a)) ≫
          (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
            (Type (u + 1))).hom.app ((forgetAb (D.obj i)).obj (FA.obj i)) := by
  rw [FA.mapTranspose_comp a b, Functor.map_comp,
    forgetAb_map_pushforward_map_comp_pushforwardComp'_hom_app]
  rfl

/-- **The underlying system of sheaves of sets** `i ↦ U(A_i)` of a system of abelian sheaves. -/
abbrev forgetSystem : EtaleSheafSystem D (Type (u + 1)) :=
  EtaleSheafSystem.ofMapTranspose (fun i => (forgetAb (D.obj i)).obj (FA.obj i))
    (fun a => (forgetAb _).map (FA.mapTranspose a)) (fun a b => forgetTransition_comp FA a b)

/-- The transposed transition maps of `forgetSystem FA` are the images under `U` of those of
`FA`. -/
theorem forgetSystem_mapTranspose {i j : Iᵒᵖ} (a : i ⟶ j) :
    (forgetSystem FA).mapTranspose a = (forgetAb _).map (FA.mapTranspose a) :=
  EtaleSheafSystem.mapTranspose_ofMapTranspose _ _ _ a

variable {c : Cone D} {𝒜 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}

/-- The underlying legs `U(A_i) ⟶ f_{i, *}U(𝒜)` of a family of legs of abelian sheaves. -/
abbrev forgetLeg
    (xA : ∀ i : Iᵒᵖ, FA.obj i ⟶ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒜)
    (i : Iᵒᵖ) :
    (forgetSystem FA).obj i ⟶
      (smallEtalePushforward (c.π.app i) (Type (u + 1))).obj ((forgetAb c.pt).obj 𝒜) :=
  (forgetAb (D.obj i)).map (xA i)

/-- The underlying shifted legs are the shifted underlying legs. -/
theorem shiftLeg_forget
    (xA : ∀ i : Iᵒᵖ, FA.obj i ⟶ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒜)
    {k j : Iᵒᵖ} (a : k ⟶ j) :
    shiftLeg (c := c) (forgetLeg FA xA) a =
      (forgetAb (D.obj j)).map (shiftLeg (c := c) xA a) := by
  simp only [shiftLeg]
  exact (forgetAb_map_pushforward_map_comp_pushforwardComp'_hom_app _ _ _ _ _).symm

/-- The underlying shifted transition maps are the shifted underlying transition maps. -/
theorem shiftTransition_forget {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j)
    (hab : ab = b ≫ a) :
    shiftTransition (Type (u + 1)) (forgetSystem FA).mapTranspose b a ab hab =
      (forgetAb (D.obj j)).map
        (shiftTransition AddCommGrpCat.{u + 1} FA.mapTranspose b a ab hab) := by
  simp only [shiftTransition, forgetSystem_mapTranspose]
  exact (forgetAb_map_pushforward_map_comp_pushforwardComp'_hom_app _ _ _ _ _).symm

/-- The underlying family of a compatible family of abelian sheaves is compatible. -/
theorem isDirCompatible_forget
    {xA : ∀ i : Iᵒᵖ, FA.obj i ⟶ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒜}
    (h : IsDirCompatible AddCommGrpCat.{u + 1} c FA 𝒜 xA) :
    IsDirCompatible (Type (u + 1)) c (forgetSystem FA) ((forgetAb c.pt).obj 𝒜)
      (forgetLeg FA xA) := by
  intro i j a
  rw [forgetSystem_mapTranspose]
  refine (congrArg (forgetAb (D.obj j)).map (h a)).trans ?_
  rw [Functor.map_comp, Functor.map_comp]
  exact congrArg (_ ≫ ·) (forgetAb_map_pushforward_map_comp_pushforwardComp'_hom_app _ _ _ _ _).symm

end ForgetSystem

/-! ### An abelian presentation in the vocabulary of the abelian development -/

section AbelianPresentation

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
  (FA : EtaleSheafSystem D AddCommGrpCat.{u + 1})
  (𝒜 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
  (xA : ∀ i : Iᵒᵖ, FA.obj i ⟶ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).obj 𝒜)

/-- The legs out of the abstract inverse images transposed to `xA`. -/
abbrev pullbackLeg (i : Iᵒᵖ) :
    (smallEtalePullbackAb (SmallEtaleLimitCohomology.conePi c i)).obj (FA.obj i) ⟶ 𝒜 :=
  ((smallEtaleAdjunctionAb (SmallEtaleLimitCohomology.conePi c i)).homEquiv _ _).symm (xA i)

/-- **An abelian presentation in adjoint form is a presentation in the sense of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`.** -/
theorem isColimitPresentation_of_isDirPresentation
    (h : IsDirPresentation AddCommGrpCat.{u + 1} c FA 𝒜 xA) :
    SmallEtaleLimitCohomology.IsColimitPresentation FA 𝒜
      (SmallEtaleLimitCohomology.untransportLeg FA 𝒜 (pullbackLeg FA 𝒜 xA)) := by
  have h' : SmallEtaleLimitCohomology.transportLeg FA 𝒜
      (SmallEtaleLimitCohomology.untransportLeg FA 𝒜 (pullbackLeg FA 𝒜 xA)) =
        pullbackLeg FA 𝒜 xA :=
    funext (SmallEtaleLimitCohomology.transportLeg_untransportLeg FA 𝒜 _)
  have hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp c a).inv.app (FA.obj j) ≫
        (smallEtalePullbackAb (c.π.app i)).map (FA.map a) ≫ pullbackLeg FA 𝒜 xA i =
          pullbackLeg FA 𝒜 xA j := fun a =>
    (compatible_iff_systemDirTransition c FA 𝒜 xA a).mpr (h.1 a)
  rw [SmallEtaleLimitCohomology.isColimitPresentation_iff,
    SmallEtaleLimitCohomology.isCompatibleFamily_iff, h']
  refine ⟨fun a => hι a, fun 𝒢 τ hτ => ?_⟩
  obtain ⟨χ, hχ, hu⟩ := h.2 𝒢 (fun i => (smallEtaleAdjunctionAb (c.π.app i)).homEquiv _ _ (τ i))
    (fun i j a => (compatible_iff_systemDirTransition c FA 𝒢
      (fun i => (smallEtaleAdjunctionAb (c.π.app i)).homEquiv _ _ (τ i)) a).mp (by
        simpa only [Equiv.symm_apply_apply] using hτ a))
  have key : ∀ (y : 𝒜 ⟶ 𝒢) (i : Iᵒᵖ),
      (smallEtaleAdjunctionAb (c.π.app i)).homEquiv _ _ (pullbackLeg FA 𝒜 xA i ≫ y) =
        xA i ≫ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).map y := fun y i =>
    (Adjunction.homEquiv_naturality_right _ _ _).trans
      (congrArg (· ≫ (smallEtalePushforwardAb (c.π.app i)).map y) (Equiv.apply_symm_apply _ _))
  refine ⟨χ, fun i => ?_, fun y hy => hu y fun i => ?_⟩
  · exact ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv _ _).injective ((key χ i).trans (hχ i))
  · exact (key y i).symm.trans (congrArg _ (hy i))

end AbelianPresentation

/-! ### The sections colimit of an abelian presentation, on the underlying sheaves of sets -/

/-- Equal images under a map of abelian groups: the difference is killed. -/
theorem hom_sub_eq_zero {G H : AddCommGrpCat.{w}} (f : G ⟶ H) (a b : ToType G) (h : f a = f b) :
    f (a - b) = 0 := by
  rw [map_sub, h, sub_self]

/-- A difference killed by a map of abelian groups: equal images. -/
theorem eq_of_hom_sub_eq_zero {G H : AddCommGrpCat.{w}} (f : G ⟶ H) (a b : ToType G)
    (h : f (a - b) = 0) : f a = f b := by
  rwa [map_sub, sub_eq_zero] at h

section ForgetSections

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D} (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (FA : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝒜 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
  (xA : ∀ i : Iᵒᵖ, FA.obj i ⟶
    (smallEtalePushforward (c.π.app i) AddCommGrpCat.{max u v + 1}).obj 𝒜)

include hc in
/-- **[Stacks, Tag 09YQ] in degree zero for an abelian presentation, read on the underlying
sheaves of sets.** For a presented system of abelian sheaves and an étale `X_{i₀}`-scheme `W`
that is quasi-compact and quasi-separated, the sections of the underlying sheaf of sets of `𝒜`
over the base change of `W` to `X` are the filtered colimit of those of the underlying sheaves of
sets of the `A_i`. -/
theorem isSectionsColimitAt_forget
    (h : IsDirPresentation AddCommGrpCat.{max u v + 1} c FA 𝒜 xA) (i₀ : I)
    (W : (D.obj (op i₀)).Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    LimitSetDirectImage.IsSectionsColimitAt (forgetSystem FA) (forgetLeg FA xA) i₀ W := by
  have : Etale W.hom := W.prop
  let E := SmallEtaleLimitCohomology.presentedSystemOfIsColimitPresentation FA 𝒜 _
    (isColimitPresentation_of_isDirPresentation FA 𝒜 xA h)
  have hlegE : LimitHigherDirectImage.legTranspose E = xA := funext fun i =>
    (congrArg ((smallEtaleAdjunctionAb (c.π.app i)).homEquiv _ _)
      (SmallEtaleLimitCohomology.transportLeg_untransportLeg FA 𝒜 _ i)).trans
        (Equiv.apply_symm_apply _ _)
  obtain ⟨hs, hz⟩ := qcqsSections_isColimit D c E i₀ W hc
  have eL : ∀ (k : (GeIndex i₀)ᵒᵖ) t,
      (shiftLeg (c := c) (forgetLeg FA xA) (geIndexToBase i₀ k)).hom.app
          (op W) t = qcqsSectionsLeg D c E i₀ W k t := by
    intro k t
    rw [shiftLeg_forget, ← LimitHigherDirectImage.shiftLeg_legTranspose_hom_app E i₀ W k, hlegE]
    rfl
  have eT : ∀ {j k : (GeIndex i₀)ᵒᵖ} (b : k ⟶ j) t,
      (shiftTransition (Type (max u v + 1)) (forgetSystem FA).mapTranspose
          ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ j) (geIndexToBase i₀ k)
          (Subsingleton.elim _ _)).hom.app (op W) t = qcqsSectionsTransition D c E i₀ W b t := by
    intro j k b t
    rw [shiftTransition_forget, ← LimitHigherDirectImage.shiftTransition_hom_app E i₀ W b]
    rfl
  refine ⟨fun s => ?_, fun k t t' htt' => ?_⟩
  · obtain ⟨k, t, ht⟩ := hs s
    exact ⟨k, t, (eL k t).trans ht⟩
  · obtain ⟨k', b, hb⟩ := hz k _ (hom_sub_eq_zero (qcqsSectionsLeg D c E i₀ W k) t t'
      ((eL k t).symm.trans (htt'.trans (eL k t'))))
    exact ⟨k', b, (eT b t).trans ((eq_of_hom_sub_eq_zero (qcqsSectionsTransition D c E i₀ W b)
      t t' hb).trans (eT b t').symm)⟩

end ForgetSections

/-! ### The units, as maps of systems -/

section Units

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
  (F : EtaleSheafSystem D (Type (u + 1)))
  {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (u + 1))).obj 𝓕)

/-- The unit `F_i ⟶ Uℤ[F_i]` commutes with the legs. -/
theorem unit_comp_forgetAb_map_freeLeg (i : Iᵒᵖ) :
    (freeAdj (D.obj i)).unit.app (F.obj i) ≫ (forgetAb (D.obj i)).map (freeLeg F x i) =
      x i ≫ (smallEtalePushforward (c.π.app i) (Type (u + 1))).map ((freeAdj c.pt).unit.app 𝓕) :=
  (unit_comp_forgetAb_map _).trans (homEquiv_freeLeg F x i)

/-- The unit `F_i ⟶ Uℤ[F_i]` commutes with the transposed transition maps. -/
theorem unit_comp_forgetSystem_mapTranspose {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeAdj (D.obj j)).unit.app (F.obj j) ≫ (forgetSystem (freeSystem F)).mapTranspose a =
      F.mapTranspose a ≫ (systemPushforward D (Type (u + 1)) a).map
        ((freeAdj (D.obj i)).unit.app (F.obj i)) := by
  rw [forgetSystem_mapTranspose, freeSystem_mapTranspose]
  exact (unit_comp_forgetAb_map _).trans (homEquiv_freeTransition F a)

/-- `ℤ[η_{F_i}]` commutes with the legs of the free systems on `F` and on `Uℤ[F]`. -/
theorem free_map_unit_comp_freeLeg (i : Iᵒᵖ) :
    (freeAb (D.obj i)).map ((freeAdj (D.obj i)).unit.app (F.obj i)) ≫
        freeLeg (forgetSystem (freeSystem F)) (forgetLeg (freeSystem F) (freeLeg F x)) i =
      freeLeg F x i ≫ (smallEtalePushforward (c.π.app i) AddCommGrpCat.{u + 1}).map
        ((freeAb c.pt).map ((freeAdj c.pt).unit.app 𝓕)) := by
  apply ((freeAdj (D.obj i)).homEquiv _ _).injective
  refine (Adjunction.homEquiv_naturality_left _ _ _).trans ?_
  refine Eq.trans ?_ (homEquiv_freeLeg_comp F x _ i).symm
  have hn := (freeAdj c.pt).unit.naturality ((freeAdj c.pt).unit.app 𝓕)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  refine (congrArg ((freeAdj (D.obj i)).unit.app (F.obj i) ≫ ·)
    (homEquiv_freeLeg (forgetSystem (freeSystem F)) (forgetLeg (freeSystem F) (freeLeg F x))
      i)).trans ?_
  refine comp_comp_eq_of_square (unit_comp_forgetAb_map_freeLeg F x i) ?_
  refine (Functor.map_comp _ _ _).symm.trans ?_
  refine congrArg (smallEtalePushforward (c.π.app i) (Type (u + 1))).map ?_
  exact hn.trans (unit_comp_forgetAb_map _)

/-- `ℤ[η_{F_i}]` commutes with the transposed transition maps of the free systems on `F` and on
`Uℤ[F]`. -/
theorem free_map_unit_comp_mapTranspose {i j : Iᵒᵖ} (a : i ⟶ j) :
    (freeAb (D.obj j)).map ((freeAdj (D.obj j)).unit.app (F.obj j)) ≫
        (freeSystem (forgetSystem (freeSystem F))).mapTranspose a =
      (freeSystem F).mapTranspose a ≫ (systemPushforward D AddCommGrpCat.{u + 1} a).map
        ((freeAb (D.obj i)).map ((freeAdj (D.obj i)).unit.app (F.obj i))) := by
  apply ((freeAdj (D.obj j)).homEquiv _ _).injective
  refine (Adjunction.homEquiv_naturality_left _ _ _).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  have hn := (freeAdj (D.obj i)).unit.naturality ((freeAdj (D.obj i)).unit.app (F.obj i))
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [freeSystem_mapTranspose, freeSystem_mapTranspose]
  refine (congrArg ((freeAdj (D.obj j)).unit.app (F.obj j) ≫ ·)
    (homEquiv_freeTransition (forgetSystem (freeSystem F)) a)).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) (homEquiv_freeTransition F a)).symm
  refine (comp_comp_eq_of_square (unit_comp_forgetSystem_mapTranspose F a) ?_).trans
    (Category.assoc _ _ _).symm
  exact ((Functor.map_comp _ _ _).symm.trans
    (congrArg (systemPushforward D (Type (u + 1)) a).map hn)).trans
      ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·)
        (forgetAb_map_pushforward_map (D.map a) _).symm))

end Units

/-! ### The sections colimit for sheaves of sets -/

/-- An equality of composites of maps of sheaves of sets, read on a section. -/
theorem sheafHom_comp_app_apply_eq {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {P Q R S : Sheaf J (Type w)} {f : P ⟶ Q} {g : Q ⟶ S} {f' : P ⟶ R} {g' : R ⟶ S}
    (h : f ≫ g = f' ≫ g') (V : Cᵒᵖ) (t : P.obj.obj V) :
    g.hom.app V (f.hom.app V t) = g'.hom.app V (f'.hom.app V t) :=
  congrArg (fun m => m.hom.app V t) h

section Main

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D} (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

include hc in
/-- **The underlying system of sheaves of sets of a presented system of abelian sheaves is
presented**: `U(𝒜) = colim f_i^{-1}U(A_i)`. This is
`Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_desc_of_sectionsColimit` fed with the
sections colimit over affine objects of `isSectionsColimitAt_forget`. -/
theorem isDirPresentation_forget (FA : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
    (𝒜 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (xA : ∀ i : Iᵒᵖ, FA.obj i ⟶
      (smallEtalePushforward (c.π.app i) AddCommGrpCat.{max u v + 1}).obj 𝒜)
    (h : IsDirPresentation AddCommGrpCat.{max u v + 1} c FA 𝒜 xA) :
    IsDirPresentation (Type (max u v + 1)) c (forgetSystem FA) ((forgetAb c.pt).obj 𝒜)
      (forgetLeg FA xA) := by
  refine ⟨isDirCompatible_forget FA h.1, fun 𝒦 τ hτ => ?_⟩
  refine LimitSetDirectImage.existsUnique_desc_of_sectionsColimit hc (forgetSystem FA)
    (forgetLeg FA xA) (fun a => isDirCompatible_forget FA h.1 a) (fun i₀ V => ?_) τ
    (fun a => hτ a)
  have : CompactSpace ((AffineEtale.Spec (D.obj (op i₀))).obj V).left :=
    inferInstanceAs (CompactSpace (Spec _))
  have : QuasiSeparatedSpace ((AffineEtale.Spec (D.obj (op i₀))).obj V).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec _))
  exact isSectionsColimitAt_forget hc FA 𝒜 xA h i₀ _

include hc in
/-- **[Stacks, Tag 09YQ] in degree zero for sheaves of sets, over a quasi-compact
quasi-separated étale object of a stage.** Let `X = lim X_i` with affine transition morphisms over
a nonempty directed set, `(F_i)` a system of sheaves of sets on the `X_i` and
`𝓕 = colim f_i^{-1}F_i` presented in adjoint form. For every étale `X_{i₀}`-scheme `W` that is
quasi-compact and quasi-separated, the sections of `𝓕` over the base change of `W` to `X` are the
filtered colimit of the sections of the `F_i`, `i ≥ i₀`, over the base changes of `W` to the `X_i`.
-/
theorem isSectionsColimitAt_of_presentation (F : EtaleSheafSystem D (Type (max u v + 1)))
    {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (max u v + 1))}
    (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (c.π.app i) (Type (max u v + 1))).obj 𝓕)
    (h : IsDirPresentation (Type (max u v + 1)) c F 𝓕 x) (i₀ : I)
    (W : (D.obj (op i₀)).Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    LimitSetDirectImage.IsSectionsColimitAt F x i₀ W := by
  have hA := isDirPresentation_free F x h
  have hUA := isDirPresentation_forget hc (freeSystem F) _ (freeLeg F x) hA
  have hB := isDirPresentation_free (forgetSystem (freeSystem F))
    (forgetLeg (freeSystem F) (freeLeg F x)) hUA
  have sA := isSectionsColimitAt_forget hc (freeSystem F) _ (freeLeg F x) hA i₀ W
  have sB := isSectionsColimitAt_forget hc (freeSystem (forgetSystem (freeSystem F))) _
    (freeLeg (forgetSystem (freeSystem F)) (forgetLeg (freeSystem F) (freeLeg F x))) hB i₀ W
  -- the units and `Uℤ[η]`, as maps of systems
  let G₁ := forgetSystem (freeSystem F)
  let G₂ := forgetSystem (freeSystem G₁)
  let xA := forgetLeg (freeSystem F) (freeLeg F x)
  let xB := forgetLeg (freeSystem G₁) (freeLeg G₁ xA)
  let η : ∀ k : Iᵒᵖ, F.obj k ⟶ G₁.obj k := fun k => (freeAdj (D.obj k)).unit.app (F.obj k)
  let η' : ∀ k : Iᵒᵖ, G₁.obj k ⟶ G₂.obj k := fun k => (freeAdj (D.obj k)).unit.app (G₁.obj k)
  let ζ : ∀ k : Iᵒᵖ, G₁.obj k ⟶ G₂.obj k :=
    fun k => (forgetAb (D.obj k)).map ((freeAb (D.obj k)).map (η k))
  let ηF := (freeAdj c.pt).unit.app 𝓕
  let ηU := (freeAdj c.pt).unit.app ((forgetAb c.pt).obj ((freeAb c.pt).obj 𝓕))
  let ζF := (forgetAb c.pt).map ((freeAb c.pt).map ηF)
  have N1η : ∀ k, η k ≫ xA k =
      x k ≫ (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).map ηF :=
    fun k => unit_comp_forgetAb_map_freeLeg F x k
  have N1η' : ∀ k, η' k ≫ xB k =
      xA k ≫ (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).map ηU :=
    fun k => unit_comp_forgetAb_map_freeLeg G₁ xA k
  have N1ζ : ∀ k, ζ k ≫ xB k =
      xA k ≫ (smallEtalePushforward (c.π.app k) (Type (max u v + 1))).map ζF := fun k =>
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (forgetAb (D.obj k)).map (free_map_unit_comp_freeLeg F x k)).trans
        (Functor.map_comp _ _ _))
  have N2η : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), η j ≫ G₁.mapTranspose a =
      F.mapTranspose a ≫ (systemPushforward D (Type (max u v + 1)) a).map (η i) :=
    fun a => unit_comp_forgetSystem_mapTranspose F a
  have N2η' : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), η' j ≫ G₂.mapTranspose a =
      G₁.mapTranspose a ≫ (systemPushforward D (Type (max u v + 1)) a).map (η' i) :=
    fun a => unit_comp_forgetSystem_mapTranspose G₁ a
  have N2ζ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), ζ j ≫ G₂.mapTranspose a =
      G₁.mapTranspose a ≫ (systemPushforward D (Type (max u v + 1)) a).map (ζ i) := by
    intro i j a
    rw [forgetSystem_mapTranspose, forgetSystem_mapTranspose]
    exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (forgetAb (D.obj j)).map (free_map_unit_comp_mapTranspose F a)).trans
        (Functor.map_comp _ _ _))
  have hnF : ηF ≫ ηU = ηF ≫ ζF := (freeAdj c.pt).unit.naturality ηF
  have cocA := fun {l k j : Iᵒᵖ} (b : l ⟶ k) (a : k ⟶ j) (ab : l ⟶ j) (hab : ab = b ≫ a) =>
    shiftTransition_comp_shiftLeg (c := c) G₁.mapTranspose xA (fun a => hUA.1 a) b a ab hab
  refine ⟨fun s => ?_, fun k t t' htt' => ?_⟩
  · -- every section comes from a level
    obtain ⟨k, t, ht⟩ := sA.1
      (((smallEtalePushforward (c.π.app (op i₀)) (Type (max u v + 1))).map ηF).hom.app (op W) s)
    have e₁ := sheafHom_comp_app_apply_eq
      (map_comp_shiftLeg xA xB η' ηU N1η' (geIndexToBase i₀ k)) (op W) t
    have e₂ := sheafHom_comp_app_apply_eq
      (map_comp_shiftLeg xA xB ζ ζF N1ζ (geIndexToBase i₀ k)) (op W) t
    have e₃ := sheafHom_comp_app_apply_eq
      ((Functor.map_comp _ _ _).symm.trans
        ((congrArg (smallEtalePushforward (c.π.app (op i₀)) (Type (max u v + 1))).map hnF).trans
          (Functor.map_comp _ _ _))) (op W) s
    rw [ht] at e₁ e₂
    obtain ⟨k', b, hb⟩ := sB.2 k _ _ (e₁.trans (e₃.trans e₂.symm))
    have f₁ := sheafHom_comp_app_apply_eq (map_comp_shiftTransition G₁.mapTranspose
      G₂.mapTranspose η' N2η' ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ k)
      (geIndexToBase i₀ k') (Subsingleton.elim _ _)) (op W) t
    have f₂ := sheafHom_comp_app_apply_eq (map_comp_shiftTransition G₁.mapTranspose
      G₂.mapTranspose ζ N2ζ ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ k)
      (geIndexToBase i₀ k') (Subsingleton.elim _ _)) (op W) t
    obtain ⟨r, hr⟩ := FreeAbelianSheaf.exists_unit_eq_of_unit_eq
      (smallEtaleTopology (D.obj ((geIndexOpFunctor i₀).obj k')))
      (F.obj ((geIndexOpFunctor i₀).obj k'))
      _ _ (f₁.symm.trans (hb.trans f₂))
    refine ⟨k', r, FreeAbelianSheaf.unit_injective _ 𝓕 _ ?_⟩
    have g₁ := sheafHom_comp_app_apply_eq
      (map_comp_shiftLeg x xA η ηF N1η (geIndexToBase i₀ k')) (op W) r
    have g₂ := sheafHom_comp_app_apply_eq
      (cocA ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ k) (geIndexToBase i₀ k')
        (Subsingleton.elim _ _)) (op W) t
    exact g₁.symm.trans ((congrArg _ hr).trans (g₂.trans ht))
  · -- two sections with the same image agree at a further level
    have g := fun t => sheafHom_comp_app_apply_eq
      (map_comp_shiftLeg x xA η ηF N1η (geIndexToBase i₀ k)) (op W) t
    obtain ⟨k', b, hb⟩ := sA.2 k _ _ ((g t).trans ((congrArg _ htt').trans (g t').symm))
    refine ⟨k', b, FreeAbelianSheaf.unit_injective _ (F.obj ((geIndexOpFunctor i₀).obj k')) _ ?_⟩
    have f := fun t => sheafHom_comp_app_apply_eq (map_comp_shiftTransition F.mapTranspose
      G₁.mapTranspose η N2η ((geIndexOpFunctor i₀).map b) (geIndexToBase i₀ k)
      (geIndexToBase i₀ k') (Subsingleton.elim _ _)) (op W) t
    exact (f t).symm.trans (hb.trans (f t'))

end Main

end SetLinearization

end Stacks.EtaleCohomology

end
