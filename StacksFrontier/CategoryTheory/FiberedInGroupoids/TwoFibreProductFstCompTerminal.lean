module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrowTerminalPullback
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Terminal arrows of the projection of a 2-fibre product to the base of its cospan

Let `p𝒴 : 𝒴 ⥤ 𝒞`, `p𝒵 : 𝒵 ⥤ 𝒞` and `p𝒳 : 𝒳 ⥤ 𝒞` be categories over `𝒞`, with `p𝒴` and `p𝒳`
fibred in groupoids, and let `a : 𝒴 ⥤ 𝒳`, `b : 𝒵 ⥤ 𝒳` be functors over `𝒞`. Write
`𝒫 = 𝒴 ×_𝒳 𝒵` for the 2-fibre product over `𝒞` (`CategoryTheory.TwoFibreProductOver`) and
`f = pr₁ ⋙ a : 𝒫 ⥤ 𝒳`.

For an object `x` of `𝒳`, a terminal arrow `(y₀, α : a y₀ ⟶ x)` of `a` at `x` and a terminal
arrow `(z₁, β : b z₁ ⟶ a y₀)` of `b` at `a y₀` together give a terminal arrow of `f` at `x`:
lift the base of `β` to `k : y' ⟶ y₀` in `𝒴`; the arrows `a k` and `β` lie over one morphism of
`𝒞`, so they differ by a unique vertical isomorphism `φ : a y' ≅ b z₁`, and the object
`(y', z₁, φ)` of `𝒫` with the arrow `a k ≫ α : a y' ⟶ x` is terminal. Its second component is
`z₁` itself. This is the statement "the base change of `x` along `f` is the base change along
`b` of the base change along `a`", read on terminal arrows, and it uses only the lifting
properties of Stacks 003S.

## Main results

* `CategoryTheory.TwoFibreProductOver.exists_isTerminal_fst_comp`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {𝒴 : Type u₁} [Category.{v₁} 𝒴]
  {𝒵 : Type u₂} [Category.{v₂} 𝒵] {𝒳 : Type u₃} [Category.{v₃} 𝒳]
  {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒵 : 𝒵 ⥤ 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞} {a : 𝒴 ⥤ 𝒳} {b : 𝒵 ⥤ 𝒳}

/-- The base morphism of a morphism of the 2-fibre product is determined by its second
component, since that component lies over it. -/
lemma Hom.hbase_eq_snd {P Q : TwoFibreProductOver p𝒴 p𝒵 p𝒳 a b} (f : P ⟶ Q) :
    f.hbase = eqToHom P.hy.symm ≫ p𝒵.map f.b ≫ eqToHom Q.hy := by
  have := f.hb
  rw [IsHomLift.fac' p𝒵 f.hbase f.b]
  simp

/-- **A terminal arrow of `pr₁ ⋙ a` from terminal arrows of `a` and of `b`.** Let `x` be an
object of `𝒳`, `ta = (y₀, α : a y₀ ⟶ x)` terminal in `CostructuredArrow a x` and
`tb = (z₁, β : b z₁ ⟶ a y₀)` terminal in `CostructuredArrow b (a y₀)`. Then there is an object
`P` of the 2-fibre product with second component `z₁` and a morphism `k : P.x ⟶ y₀` with
`P.iso ≫ β = a k`, such that `(P, a k ≫ α)` is terminal in `CostructuredArrow (pr₁ ⋙ a) x`. -/
theorem exists_isTerminal_fst_comp (hp𝒴 : p𝒴.IsFiberedInGroupoids)
    (hp𝒳 : p𝒳.IsFiberedInGroupoids) (ha : a ⋙ p𝒳 = p𝒴) (hb : b ⋙ p𝒳 = p𝒵) {x : 𝒳}
    {ta : CostructuredArrow a x} (hta : IsTerminal ta)
    {tb : CostructuredArrow b (a.obj ta.left)} (htb : IsTerminal tb) :
    ∃ (P : TwoFibreProductOver p𝒴 p𝒵 p𝒳 a b) (k : P.x ⟶ ta.left) (hPy : P.y = tb.left),
      P.iso.hom ≫ b.map (eqToHom hPy) ≫ tb.hom = a.map k ∧
      Nonempty (IsTerminal (CostructuredArrow.mk (Y := P) (a.map k ≫ ta.hom) :
        CostructuredArrow (fst p𝒴 p𝒵 p𝒳 a b ⋙ a) x)) := by
  subst ha hb
  obtain ⟨y', hy', k, hk⟩ := hp𝒴.exists_lift_eqToHom ta.left (p𝒳.map tb.hom)
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := hp𝒳.unique_lift tb.hom (a.map k) (eqToHom hy') hk.symm
  have hφlift : p𝒳.IsHomLift (𝟙 (p𝒳.obj (b.obj tb.left))) φ :=
    IsHomLift.of_fac' p𝒳 _ φ hy' rfl (by simp [hφ₁])
  have : p𝒳.IsStronglyCartesian (𝟙 (p𝒳.obj (b.obj tb.left))) φ :=
    hp𝒳.isStronglyCartesian_homLift _ φ
  have : IsIso φ := Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p𝒳)
    (f := 𝟙 (p𝒳.obj (b.obj tb.left))) φ
  let P : TwoFibreProductOver (a ⋙ p𝒳) (b ⋙ p𝒳) p𝒳 a b :=
    ⟨p𝒳.obj (b.obj tb.left), y', tb.left, hy', rfl, asIso φ, hφlift⟩
  have H : ∀ c : CostructuredArrow (fst (a ⋙ p𝒳) (b ⋙ p𝒳) p𝒳 a b ⋙ a) x,
      ∃! _m : c ⟶ (CostructuredArrow.mk (Y := P) (a.map k ≫ ta.hom) :
        CostructuredArrow (fst (a ⋙ p𝒳) (b ⋙ p𝒳) p𝒳 a b ⋙ a) x), True := by
    intro c
    -- the two components of the morphism out of `c`, from the terminality of `ta` and `tb`
    let ca : CostructuredArrow a x := .mk (Y := c.left.x) c.hom
    let u₁ := (hta.from ca).left
    have hu₁ : a.map u₁ ≫ ta.hom = c.hom := CostructuredArrow.w (hta.from ca)
    let cb : CostructuredArrow b (a.obj ta.left) :=
      .mk (Y := c.left.y) (c.left.iso.inv ≫ a.map u₁)
    let u₂ := (htb.from cb).left
    have hu₂ : b.map u₂ ≫ tb.hom = c.left.iso.inv ≫ a.map u₁ := CostructuredArrow.w (htb.from cb)
    have := c.left.vertical
    have hvinv : p𝒳.map c.left.iso.inv = eqToHom (c.left.hy.trans c.left.hx.symm) := by
      rw [IsHomLift.fac' p𝒳 (𝟙 c.left.base) c.left.iso.inv]
      simp
    have hvhom : p𝒳.map c.left.iso.hom = eqToHom (c.left.hx.trans c.left.hy.symm) := by
      rw [IsHomLift.fac' p𝒳 (𝟙 c.left.base) c.left.iso.hom]
      simp
    let g : (a ⋙ p𝒳).obj c.left.x ⟶ (a ⋙ p𝒳).obj y' :=
      eqToHom (c.left.hx.trans c.left.hy.symm) ≫ p𝒳.map (b.map u₂) ≫ eqToHom hy'.symm
    have hg : g ≫ (a ⋙ p𝒳).map k = (a ⋙ p𝒳).map u₁ := by
      change g ≫ p𝒳.map (a.map k) = p𝒳.map (a.map u₁)
      have h1 : p𝒳.map (a.map k) = eqToHom hy' ≫ p𝒳.map tb.hom := hk
      have h2 : p𝒳.map (b.map u₂) ≫ p𝒳.map tb.hom =
          p𝒳.map c.left.iso.inv ≫ p𝒳.map (a.map u₁) := by
        rw [← p𝒳.map_comp, hu₂, p𝒳.map_comp]
      simp only [g, h1, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [h2, hvinv, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    obtain ⟨ma, ⟨hma₁, hma₂⟩, hmau⟩ := hp𝒴.unique_lift k u₁ g hg
    refine ⟨CostructuredArrow.homMk (Hom.mk' (P := c.left) (Q := P) ma u₂ ?_ ?_) ?_, trivial,
      fun m _ => ?_⟩
    · change eqToHom c.left.hy.symm ≫ p𝒳.map (b.map u₂) ≫ eqToHom rfl =
        eqToHom c.left.hx.symm ≫ (a ⋙ p𝒳).map ma ≫ eqToHom hy'
      rw [hma₁]
      simp [g]
    · change a.map ma ≫ φ = c.left.iso.hom ≫ b.map u₂
      refine (hp𝒳.unique_lift tb.hom (a.map u₁) (p𝒳.map (a.map ma ≫ φ)) ?_).unique
        ⟨rfl, ?_⟩ ⟨?_, ?_⟩
      · rw [← p𝒳.map_comp, Category.assoc, hφ₂, ← a.map_comp, hma₂]
      · rw [Category.assoc, hφ₂, ← a.map_comp, hma₂]
      · rw [p𝒳.map_comp, p𝒳.map_comp, hφ₁, hvhom,
          show p𝒳.map (a.map ma) = g from hma₁]
        simp [g]
      · rw [Category.assoc, hu₂, Iso.hom_inv_id_assoc]
    · change a.map ma ≫ a.map k ≫ ta.hom = c.hom
      rw [← a.map_comp_assoc, hma₂, hu₁]
    · -- uniqueness
      have hm : (fst _ _ _ a b ⋙ a).map m.left ≫ (a.map k ≫ ta.hom) = c.hom := CostructuredArrow.w m
      have hmk : m.left.a ≫ k = u₁ := congrArg CommaMorphism.left
        (hta.hom_ext (CostructuredArrow.homMk (m.left.a ≫ k) (by
          change a.map (m.left.a ≫ k) ≫ ta.hom = c.hom
          rw [a.map_comp, Category.assoc]
          exact hm) : ca ⟶ ta) (hta.from ca))
      have hmw : a.map m.left.a ≫ φ = c.left.iso.hom ≫ b.map m.left.b := m.left.w
      have hmb : m.left.b = u₂ := congrArg CommaMorphism.left
        (htb.hom_ext (CostructuredArrow.homMk m.left.b (by
          change b.map m.left.b ≫ tb.hom = c.left.iso.inv ≫ a.map u₁
          have hb' : b.map m.left.b = c.left.iso.inv ≫ a.map m.left.a ≫ φ := by
            rw [hmw, Iso.inv_hom_id_assoc]
          rw [hb', Category.assoc, Category.assoc, hφ₂, ← a.map_comp, hmk]) :
            cb ⟶ tb) (htb.from cb))
      have hma : m.left.a = ma := by
        refine hmau m.left.a ⟨?_, hmk⟩
        have h1 := Hom.hbase_eq m.left
        have h2 := Hom.hbase_eq_snd m.left
        change (a ⋙ p𝒳).map m.left.a = g
        have h3 : (a ⋙ p𝒳).map m.left.a =
            eqToHom c.left.hx ≫ m.left.hbase ≫ eqToHom hy'.symm := by
          rw [h1]
          simp
        rw [h3, h2, hmb]
        simp [g]
      refine CostructuredArrow.hom_ext _ _ (Hom.ext' ?_ ?_)
      · exact hma
      · exact hmb
  exact ⟨P, k, rfl, by simpa [P] using hφ₂, ⟨IsTerminal.ofUniqueHom
    (fun c => (H c).exists.choose) (fun c m => (H c).unique trivial (H c).exists.choose_spec)⟩⟩

end CategoryTheory.TwoFibreProductOver

end
