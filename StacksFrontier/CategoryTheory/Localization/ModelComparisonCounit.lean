module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Iso

/-!
# Comparisons of two models of derived adjunctions

Consider an adjunction `p ⊣ q` of underived functors and, at two models `D¹`, `D²` of the
localized categories (localization functors `Q¹`, `Q²` identified by `κ : Q¹ ⋙ E ≅ Q²` through a
comparison functor `E`), derived adjunctions `L¹ ⊣ R¹` and `L² ⊣ R²` whose counits are compatible
with that of `p ⊣ q` through the comparisons `c` and `η` of derived and underived functors. The
identifications `φ : L¹ ⋙ E ≅ E ⋙ L²` and `ψ : R¹ ⋙ E ≅ E ⋙ R²` of the two models, characterized
by their compatibility with `c` and `η`, are then compatible with the two counits. Similarly the
identifications `φ` are compatible with the composition isomorphisms of the derived functors.

## Main results

* `Stacks.CategoryTheory.ModelComparison.counit_comm` — compatibility with the counits.
* `Stacks.CategoryTheory.ModelComparison.comp_comm` — compatibility with composition.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.ModelComparison

variable {HX HY D₁X D₂X D₁Y D₂Y : Type*} [Category HX] [Category HY]
  [Category D₁X] [Category D₂X] [Category D₁Y] [Category D₂Y]
  {Q₁X : HX ⥤ D₁X} {Q₂X : HX ⥤ D₂X} {Q₁Y : HY ⥤ D₁Y} {Q₂Y : HY ⥤ D₂Y}
  {EX : D₁X ⥤ D₂X} {EY : D₁Y ⥤ D₂Y}
  (κX : Q₁X ⋙ EX ≅ Q₂X) (κY : Q₁Y ⋙ EY ≅ Q₂Y)

/-- Two natural transformations that agree at `K'` agree at every object `K` isomorphic to it. -/
private theorem app_eq_of_iso_app_eq {S T : Type*} [Category S] [Category T] {F G : S ⥤ T}
    (α β : F ⟶ G) {K K' : S} (e : K ≅ K') (h : α.app K' = β.app K') : α.app K = β.app K := by
  rw [← cancel_epi (F.map e.inv), α.naturality, β.naturality, h]

section Counit

variable {p : HY ⥤ HX} {q : HX ⥤ HY} (a : p ⊣ q)
  {L₁ : D₁Y ⥤ D₁X} {R₁ : D₁X ⥤ D₁Y} {L₂ : D₂Y ⥤ D₂X} {R₂ : D₂X ⥤ D₂Y}
  (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂)
  (c₁ : Q₁Y ⋙ L₁ ⟶ p ⋙ Q₁X) (c₂ : Q₂Y ⋙ L₂ ⟶ p ⋙ Q₂X)
  (η₁ : q ⋙ Q₁Y ⟶ Q₁X ⋙ R₁) (η₂ : q ⋙ Q₂Y ⟶ Q₂X ⋙ R₂)
  (φ : L₁ ⋙ EX ≅ EY ⋙ L₂) (ψ : R₁ ⋙ EY ≅ EX ⋙ R₂)

/-- **The two models of a derived adjunction have compatible counits.** If both derived counits
are compatible with the underived counit (`h₁`, `h₂`), `φ` and `ψ` are compatible with the
comparisons (`hφ`, `hψ`), and every object is, up to isomorphism, the image of one at which `η₁`
is invertible (`hres`), then `L₂(ψ) ≫ ε₂ = φ⁻¹ ≫ E(ε₁)`. -/
theorem counit_comm
    (h₁ : ∀ N : HX, L₁.map (η₁.app N) ≫ A₁.counit.app (Q₁X.obj N) =
      c₁.app (q.obj N) ≫ Q₁X.map (a.counit.app N))
    (h₂ : ∀ N : HX, L₂.map (η₂.app N) ≫ A₂.counit.app (Q₂X.obj N) =
      c₂.app (q.obj N) ≫ Q₂X.map (a.counit.app N))
    (hφ : ∀ M : HY, φ.hom.app (Q₁Y.obj M) ≫ L₂.map (κY.hom.app M) ≫ c₂.app M =
      EX.map (c₁.app M) ≫ κX.hom.app (p.obj M))
    (hψ : ∀ N : HX, EY.map (η₁.app N) ≫ ψ.hom.app (Q₁X.obj N) =
      κY.hom.app (q.obj N) ≫ η₂.app N ≫ R₂.map (κX.inv.app N))
    (hres : ∀ K : D₁X, ∃ (N : HX) (_ : K ≅ Q₁X.obj N), IsIso (η₁.app N))
    (K : D₁X) :
    L₂.map (ψ.hom.app K) ≫ A₂.counit.app (EX.obj K) =
      φ.inv.app (R₁.obj K) ≫ EX.map (A₁.counit.app K) := by
  obtain ⟨N, e, hN⟩ := hres K
  let α : R₁ ⋙ EY ⋙ L₂ ⟶ EX :=
    { app := fun K => L₂.map (ψ.hom.app K) ≫ A₂.counit.app (EX.obj K)
      naturality := fun K K' u => by
        have h1 := ψ.hom.naturality u
        have h2 := A₂.counit.naturality (EX.map u)
        simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at h1 h2 ⊢
        rw [← L₂.map_comp_assoc, h1, L₂.map_comp, Category.assoc, h2, Category.assoc] }
  let β : R₁ ⋙ EY ⋙ L₂ ⟶ EX :=
    { app := fun K => φ.inv.app (R₁.obj K) ≫ EX.map (A₁.counit.app K)
      naturality := fun K K' u => by
        have h1 := φ.inv.naturality (R₁.map u)
        have h2 := A₁.counit.naturality u
        simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at h1 h2 ⊢
        rw [reassoc_of% h1, ← EX.map_comp, Category.assoc, ← EX.map_comp, h2] }
  refine app_eq_of_iso_app_eq α β e ?_
  change L₂.map (ψ.hom.app (Q₁X.obj N)) ≫ A₂.counit.app (EX.obj (Q₁X.obj N)) =
    φ.inv.app (R₁.obj (Q₁X.obj N)) ≫ EX.map (A₁.counit.app (Q₁X.obj N))
  rw [← cancel_epi (L₂.map (EY.map (η₁.app N)))]
  have hl : L₂.map (EY.map (η₁.app N)) ≫ L₂.map (ψ.hom.app (Q₁X.obj N)) ≫
      A₂.counit.app (EX.obj (Q₁X.obj N)) =
      L₂.map (κY.hom.app (q.obj N)) ≫ c₂.app (q.obj N) ≫ Q₂X.map (a.counit.app N) ≫
        κX.inv.app N := by
    rw [← L₂.map_comp_assoc, hψ, L₂.map_comp, L₂.map_comp, Category.assoc, Category.assoc]
    have hn := A₂.counit.naturality (κX.inv.app N)
    simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn, reassoc_of% h₂ N]
  have hr : L₂.map (EY.map (η₁.app N)) ≫ φ.inv.app (R₁.obj (Q₁X.obj N)) ≫
      EX.map (A₁.counit.app (Q₁X.obj N)) =
      φ.inv.app (Q₁Y.obj (q.obj N)) ≫ EX.map (c₁.app (q.obj N)) ≫
        EX.map (Q₁X.map (a.counit.app N)) := by
    have hn := φ.inv.naturality (η₁.app N)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [reassoc_of% hn, ← EX.map_comp, h₁ N, EX.map_comp]
  rw [hl, hr]
  have hφ' := hφ (q.obj N)
  rw [← cancel_epi (φ.hom.app (Q₁Y.obj (q.obj N))), Iso.hom_inv_id_app_assoc, reassoc_of% hφ']
  have hk := κX.hom.naturality (a.counit.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at hk
  rw [← reassoc_of% hk, Iso.hom_inv_id_app]
  exact congrArg (EX.map (c₁.app (q.obj N)) ≫ ·) (Category.comp_id _)

end Counit

section Comp

variable {HZ D₁Z D₂Z : Type*} [Category HZ] [Category D₁Z] [Category D₂Z]
  {Q₁Z : HZ ⥤ D₁Z} {Q₂Z : HZ ⥤ D₂Z} {EZ : D₁Z ⥤ D₂Z} (κZ : Q₁Z ⋙ EZ ≅ Q₂Z)
  {pf : HY ⥤ HX} {pg : HZ ⥤ HY} {pc : HZ ⥤ HX} (e : pg ⋙ pf ≅ pc)
  {L₁f : D₁Y ⥤ D₁X} {L₁g : D₁Z ⥤ D₁Y} {L₁c : D₁Z ⥤ D₁X}
  {L₂f : D₂Y ⥤ D₂X} {L₂g : D₂Z ⥤ D₂Y} {L₂c : D₂Z ⥤ D₂X}
  (C₁ : L₁g ⋙ L₁f ≅ L₁c) (C₂ : L₂g ⋙ L₂f ≅ L₂c)
  (c₁f : Q₁Y ⋙ L₁f ⟶ pf ⋙ Q₁X) (c₁g : Q₁Z ⋙ L₁g ⟶ pg ⋙ Q₁Y) (c₁c : Q₁Z ⋙ L₁c ⟶ pc ⋙ Q₁X)
  (c₂f : Q₂Y ⋙ L₂f ⟶ pf ⋙ Q₂X) (c₂g : Q₂Z ⋙ L₂g ⟶ pg ⋙ Q₂Y) (c₂c : Q₂Z ⋙ L₂c ⟶ pc ⋙ Q₂X)
  (φf : L₁f ⋙ EX ≅ EY ⋙ L₂f) (φg : L₁g ⋙ EY ≅ EZ ⋙ L₂g) (φc : L₁c ⋙ EX ≅ EZ ⋙ L₂c)

/-- **The two models of derived pullback have compatible composition isomorphisms.** If both
composition isomorphisms are compatible with the comparisons of derived and underived functors
(`h₁`, `h₂`), the identifications `φ` are compatible with the comparisons (`hf`, `hg`, `hc`), and
every object is, up to isomorphism, the image of one at which `c₁c` is invertible (`hres`), then
the identification of the composite is the composite of the identifications. -/
theorem comp_comm
    (h₁ : ∀ M : HZ, C₁.hom.app (Q₁Z.obj M) ≫ c₁c.app M =
      L₁f.map (c₁g.app M) ≫ c₁f.app (pg.obj M) ≫ Q₁X.map (e.hom.app M))
    (h₂ : ∀ M : HZ, C₂.hom.app (Q₂Z.obj M) ≫ c₂c.app M =
      L₂f.map (c₂g.app M) ≫ c₂f.app (pg.obj M) ≫ Q₂X.map (e.hom.app M))
    (hf : ∀ M : HY, φf.hom.app (Q₁Y.obj M) ≫ L₂f.map (κY.hom.app M) ≫ c₂f.app M =
      EX.map (c₁f.app M) ≫ κX.hom.app (pf.obj M))
    (hg : ∀ M : HZ, φg.hom.app (Q₁Z.obj M) ≫ L₂g.map (κZ.hom.app M) ≫ c₂g.app M =
      EY.map (c₁g.app M) ≫ κY.hom.app (pg.obj M))
    (hc : ∀ M : HZ, φc.hom.app (Q₁Z.obj M) ≫ L₂c.map (κZ.hom.app M) ≫ c₂c.app M =
      EX.map (c₁c.app M) ≫ κX.hom.app (pc.obj M))
    (hres : ∀ K : D₁Z, ∃ (M : HZ) (_ : K ≅ Q₁Z.obj M), IsIso (c₁c.app M))
    (K : D₁Z) :
    C₂.hom.app (EZ.obj K) ≫ φc.inv.app K =
      L₂f.map (φg.inv.app K) ≫ φf.inv.app (L₁g.obj K) ≫ EX.map (C₁.hom.app K) := by
  obtain ⟨M, i, hM⟩ := hres K
  let α : EZ ⋙ L₂g ⋙ L₂f ⟶ L₁c ⋙ EX :=
    { app := fun K => C₂.hom.app (EZ.obj K) ≫ φc.inv.app K
      naturality := fun K K' u => by
        have n1 := C₂.hom.naturality (EZ.map u)
        have n2 := φc.inv.naturality u
        simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 ⊢
        rw [reassoc_of% n1, n2, Category.assoc] }
  let β : EZ ⋙ L₂g ⋙ L₂f ⟶ L₁c ⋙ EX :=
    { app := fun K => L₂f.map (φg.inv.app K) ≫ φf.inv.app (L₁g.obj K) ≫ EX.map (C₁.hom.app K)
      naturality := fun K K' u => by
        have n1 := φg.inv.naturality u
        have n2 := φf.inv.naturality (L₁g.map u)
        have n3 := C₁.hom.naturality u
        simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 ⊢
        rw [← L₂f.map_comp_assoc, n1, L₂f.map_comp, Category.assoc, reassoc_of% n2,
          ← EX.map_comp, n3, EX.map_comp]
        simp only [Category.assoc] }
  refine app_eq_of_iso_app_eq α β i ?_
  change C₂.hom.app (EZ.obj (Q₁Z.obj M)) ≫ φc.inv.app (Q₁Z.obj M) =
    L₂f.map (φg.inv.app (Q₁Z.obj M)) ≫ φf.inv.app (L₁g.obj (Q₁Z.obj M)) ≫
      EX.map (C₁.hom.app (Q₁Z.obj M))
  rw [← cancel_mono (EX.map (c₁c.app M) ≫ κX.hom.app (pc.obj M))]
  have hl : C₂.hom.app (EZ.obj (Q₁Z.obj M)) ≫ φc.inv.app (Q₁Z.obj M) ≫ EX.map (c₁c.app M) ≫
      κX.hom.app (pc.obj M) = L₂f.map (L₂g.map (κZ.hom.app M)) ≫ L₂f.map (c₂g.app M) ≫
        c₂f.app (pg.obj M) ≫ Q₂X.map (e.hom.app M) := by
    rw [← hc M, Iso.inv_hom_id_app_assoc]
    have n := C₂.hom.naturality (κZ.hom.app M)
    simp only [Functor.comp_obj, Functor.comp_map] at n
    rw [← reassoc_of% n, h₂ M]
  have hφg : φg.inv.app (Q₁Z.obj M) ≫ EY.map (c₁g.app M) ≫ κY.hom.app (pg.obj M) =
      L₂g.map (κZ.hom.app M) ≫ c₂g.app M := by
    rw [← hg M, Iso.inv_hom_id_app_assoc]
  have hφf : φf.inv.app (Q₁Y.obj (pg.obj M)) ≫ EX.map (c₁f.app (pg.obj M)) ≫
      κX.hom.app (pf.obj (pg.obj M)) = L₂f.map (κY.hom.app (pg.obj M)) ≫ c₂f.app (pg.obj M) := by
    rw [← hf (pg.obj M), Iso.inv_hom_id_app_assoc]
  have nf := φf.inv.naturality (c₁g.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at nf
  have nκ := κX.hom.naturality (e.hom.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at nκ
  have hr : L₂f.map (φg.inv.app (Q₁Z.obj M)) ≫ φf.inv.app (L₁g.obj (Q₁Z.obj M)) ≫
      EX.map (C₁.hom.app (Q₁Z.obj M)) ≫ EX.map (c₁c.app M) ≫ κX.hom.app (pc.obj M) =
      L₂f.map (L₂g.map (κZ.hom.app M)) ≫ L₂f.map (c₂g.app M) ≫
        c₂f.app (pg.obj M) ≫ Q₂X.map (e.hom.app M) := by
    rw [← EX.map_comp_assoc, h₁ M, EX.map_comp, EX.map_comp]
    simp only [Category.assoc]
    rw [nκ, ← reassoc_of% nf, reassoc_of% hφf, ← L₂f.map_comp_assoc,
      ← L₂f.map_comp_assoc, Category.assoc, hφg, L₂f.map_comp, Category.assoc]
  simp only [Category.assoc]
  rw [hl, hr]

end Comp

end Stacks.CategoryTheory.ModelComparison
