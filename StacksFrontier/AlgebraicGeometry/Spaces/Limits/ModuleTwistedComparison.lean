module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleHomRestrictionTwoSided

/-!
# The canonical comparison twisted by an identification with a pulled-back module

Let `ell : W ⟶ X` and `π : W ⟶ U` be morphisms of algebraic spaces, `P` an `𝒪_X`-module, `G` an
`𝒪_U`-module and `η : ell^*P ≅ π^*G`.  For two morphisms `a, b : T ⟶ W` with
`a ≫ ell = b ≫ ell = t` the identity of `t^*P` transports along the restrictions of `η` to a
morphism `(a ≫ π)^*G ⟶ (b ≫ π)^*G`: the canonical comparison of Stacks 04W5 read through `η`.
This file records that twisted comparison and its three properties: it is stable under
restriction, it composes, and it is the identity on the diagonal.  These are what makes the
descent datum of a module given on a chart satisfy the cocycle condition.

## Main definitions

* `AlgebraicGeometry.Space.twistedComparison`: the twisted comparison.

## Main results

* `AlgebraicGeometry.Space.moduleHomRestrict₂_twistedComparison`: stability under restriction.
* `AlgebraicGeometry.Space.twistedComparison_comp`: composition.
* `AlgebraicGeometry.Space.twistedComparison_self`: the identity on the diagonal.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X U W : AlgebraicSpaces B S hS} (ell : W ⟶ X) (π : W ⟶ U)
  {P : Modules.{u, u} B S hS X.1 X.2} {G : Modules.{u, u} B S hS U.1 U.2}
  (η : (modulePullback B S hS ell).obj P ≅ (modulePullback B S hS π).obj G)

/-- The identity of `t^*P`, for `t = a ≫ ell = b ≫ ell`, transported along the restrictions of
`η` along `a` and `b` to a morphism `(a ≫ π)^*G ⟶ (b ≫ π)^*G`. -/
noncomputable def twistedComparison {T : AlgebraicSpaces B S hS} (a b : T ⟶ W) (t : T ⟶ X)
    (va vb : T ⟶ U) (ha : a ≫ ell = t) (hb : b ≫ ell = t) (hva : a ≫ π = va)
    (hvb : b ≫ π = vb) :
    (modulePullback B S hS va).obj G ⟶ (modulePullback B S hS vb).obj G :=
  moduleHomRestrict₂ G P a π ell va t hva ha η.inv ≫
    moduleHomRestrict₂ P G b ell π t vb hb hvb η.hom

/-- **The twisted comparisons compose.** -/
theorem twistedComparison_comp {T : AlgebraicSpaces B S hS} (a b c : T ⟶ W) (t : T ⟶ X)
    (va vb vc : T ⟶ U) (ha : a ≫ ell = t) (hb : b ≫ ell = t) (hc : c ≫ ell = t)
    (hva : a ≫ π = va) (hvb : b ≫ π = vb) (hvc : c ≫ π = vc) :
    twistedComparison ell π η a b t va vb ha hb hva hvb ≫
        twistedComparison ell π η b c t vb vc hb hc hvb hvc =
      twistedComparison ell π η a c t va vc ha hc hva hvc := by
  simp only [twistedComparison, Category.assoc]
  rw [← Category.assoc (moduleHomRestrict₂ P G b ell π t vb hb hvb η.hom),
    ← moduleHomRestrict₂_comp, η.hom_inv_id, moduleHomRestrict₂_id, Category.id_comp]

/-- **The twisted comparison is the identity on the diagonal.** -/
theorem twistedComparison_self {T : AlgebraicSpaces B S hS} (a : T ⟶ W) (t : T ⟶ X)
    (va : T ⟶ U) (ha : a ≫ ell = t) (hva : a ≫ π = va) :
    twistedComparison ell π η a a t va va ha ha hva hva = 𝟙 _ := by
  rw [twistedComparison, ← moduleHomRestrict₂_comp, η.inv_hom_id, moduleHomRestrict₂_id]

/-- **The twisted comparison is stable under restriction.** -/
theorem moduleHomRestrict₂_twistedComparison {T T' : AlgebraicSpaces B S hS} (z : T' ⟶ T)
    (a b : T ⟶ W) (t : T ⟶ X) (va vb : T ⟶ U) (ha : a ≫ ell = t) (hb : b ≫ ell = t)
    (hva : a ≫ π = va) (hvb : b ≫ π = vb) (a' b' : T' ⟶ W) (t' : T' ⟶ X) (va' vb' : T' ⟶ U)
    (hza : z ≫ a = a') (hzb : z ≫ b = b') (hzt : z ≫ t = t') (hzva : z ≫ va = va')
    (hzvb : z ≫ vb = vb') (ha' : a' ≫ ell = t') (hb' : b' ≫ ell = t') (hva' : a' ≫ π = va')
    (hvb' : b' ≫ π = vb') :
    moduleHomRestrict₂ G G z va vb va' vb' hzva hzvb
        (twistedComparison ell π η a b t va vb ha hb hva hvb) =
      twistedComparison ell π η a' b' t' va' vb' ha' hb' hva' hvb' := by
  subst hza hzb hzt hzva hzvb hva hvb ha
  have e1 := moduleHomRestrict₂_moduleHomRestrict₂ (M := G) (N := P) a z (z ≫ a) rfl π ell
    (a ≫ π) (a ≫ ell) (z ≫ a ≫ π) (z ≫ a ≫ ell) rfl rfl rfl rfl η.inv
  have e2 := moduleHomRestrict₂_moduleHomRestrict₂ (M := P) (N := G) b z (z ≫ b) rfl ell π
    (a ≫ ell) (b ≫ π) (z ≫ a ≫ ell) (z ≫ b ≫ π) hb rfl rfl rfl η.hom
  have e3 := moduleHomRestrict₂_comp (K := G) z (a ≫ π) (a ≫ ell) (b ≫ π)
    (z ≫ a ≫ π) (z ≫ a ≫ ell) (z ≫ b ≫ π) rfl rfl rfl
    (moduleHomRestrict₂ G P a π ell (a ≫ π) (a ≫ ell) rfl rfl η.inv)
    (moduleHomRestrict₂ P G b ell π (a ≫ ell) (b ≫ π) hb rfl η.hom)
  exact e3.trans (congrArg₂ (· ≫ ·) e1 e2)

/-- The twisted comparison, as an isomorphism. -/
noncomputable def twistedComparisonIso {T : AlgebraicSpaces B S hS} (a b : T ⟶ W) (t : T ⟶ X)
    (va vb : T ⟶ U) (ha : a ≫ ell = t) (hb : b ≫ ell = t) (hva : a ≫ π = va)
    (hvb : b ≫ π = vb) :
    (modulePullback B S hS va).obj G ≅ (modulePullback B S hS vb).obj G where
  hom := twistedComparison ell π η a b t va vb ha hb hva hvb
  inv := twistedComparison ell π η b a t vb va hb ha hvb hva
  hom_inv_id := by rw [twistedComparison_comp, twistedComparison_self]
  inv_hom_id := by rw [twistedComparison_comp, twistedComparison_self]

/-- The cancellation behind `moduleHomRestrict_eq_of_twistedComparison_eq`, with every object
and morphism abstract. -/
theorem descent_aux {C : Type*} [Category C] {A A' Va Vb : C} (i₁ : A ≅ Va) (i₂ : A' ≅ Va)
    (j₁ : A ≅ Vb) (j₂ : A' ≅ Vb) (h : i₁.inv ≫ j₁.hom = i₂.inv ≫ j₂.hom) :
    i₁.hom ≫ i₂.inv = j₁.hom ≫ j₂.inv := by
  have h' := congrArg (fun z => i₁.hom ≫ z ≫ j₂.inv) h
  simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact h'.symm

/-- **Two identifications with the same twisted comparisons give a morphism satisfying the descent
condition.**  If `ζ₁ : ell^*P₁ ≅ π^*G` and `ζ₂ : ell^*P₂ ≅ π^*G` have the same twisted comparison
at a pair `a, b` with `a ≫ ell = b ≫ ell`, then the two restrictions of `ζ₁ ≫ ζ₂⁻¹` along `a`
and `b` agree. -/
theorem moduleHomRestrict_eq_of_twistedComparison_eq {P₁ P₂ : Modules.{u, u} B S hS X.1 X.2}
    (ζ₁ : (modulePullback B S hS ell).obj P₁ ≅ (modulePullback B S hS π).obj G)
    (ζ₂ : (modulePullback B S hS ell).obj P₂ ≅ (modulePullback B S hS π).obj G)
    {T : AlgebraicSpaces B S hS} (a b : T ⟶ W) (t : T ⟶ X) (ha : a ≫ ell = t)
    (hb : b ≫ ell = t)
    (h : twistedComparison ell π ζ₁ a b t (a ≫ π) (b ≫ π) ha hb rfl rfl =
      twistedComparison ell π ζ₂ a b t (a ≫ π) (b ≫ π) ha hb rfl rfl) :
    moduleHomRestrict P₁ P₂ a ell t ha (ζ₁.hom ≫ ζ₂.inv) =
      moduleHomRestrict P₁ P₂ b ell t hb (ζ₁.hom ≫ ζ₂.inv) := by
  rw [← moduleHomRestrict₂_self, ← moduleHomRestrict₂_self,
    moduleHomRestrict₂_comp a ell π ell t (a ≫ π) t ha rfl ha,
    moduleHomRestrict₂_comp b ell π ell t (b ≫ π) t hb rfl hb]
  exact descent_aux (moduleIsoRestrict₂ a ell π t (a ≫ π) ha rfl ζ₁)
    (moduleIsoRestrict₂ a ell π t (a ≫ π) ha rfl ζ₂)
    (moduleIsoRestrict₂ b ell π t (b ≫ π) hb rfl ζ₁)
    (moduleIsoRestrict₂ b ell π t (b ≫ π) hb rfl ζ₂) h

omit η in
/-- If `w ≫ pp = a ≫ cl`, `cl ≫ u = π` and `a ≫ π = va`, then `w ≫ pp ≫ u = va`. -/
theorem twistedTransition_aux {T Sp Um : AlgebraicSpaces B S hS} (w : T ⟶ Sp) (pp : Sp ⟶ Um)
    (cl : W ⟶ Um) (a : T ⟶ W) (u : Um ⟶ U) (va : T ⟶ U) (hw : w ≫ pp = a ≫ cl)
    (hπ : cl ≫ u = π) (hva : a ≫ π = va) : w ≫ pp ≫ u = va := by
  rw [← Category.assoc, hw, Category.assoc, hπ, hva]

/-- **Twisted transition morphisms.**  Let `ppF, ppS : Sp ⟶ Um` be two morphisms and
`cl : W ⟶ Um`, `u : Um ⟶ U` with `cl ≫ u = π`.  A morphism `ψ : (ppF ≫ u)^*G ⟶ (ppS ≫ u)^*G`
is a twisted transition morphism when its restriction along every `w : T ⟶ Sp` lying over two
morphisms `a, b : T ⟶ W` with `a ≫ ell = b ≫ ell` is the twisted comparison of `η` at `a, b`. -/
def IsTwistedTransition {Sp Um : AlgebraicSpaces B S hS} (ppF ppS : Sp ⟶ Um) (cl : W ⟶ Um)
    (u : Um ⟶ U) (hπ : cl ≫ u = π)
    (ψ : (modulePullback B S hS (ppF ≫ u)).obj G ⟶ (modulePullback B S hS (ppS ≫ u)).obj G) :
    Prop :=
  ∀ (T : AlgebraicSpaces B S hS) (a b : T ⟶ W) (t : T ⟶ X) (ha : a ≫ ell = t)
    (hb : b ≫ ell = t) (w : T ⟶ Sp) (hw₁ : w ≫ ppF = a ≫ cl) (hw₂ : w ≫ ppS = b ≫ cl)
    (va vb : T ⟶ U) (hva : a ≫ π = va) (hvb : b ≫ π = vb),
    moduleHomRestrict₂ G G w (ppF ≫ u) (ppS ≫ u) va vb
        (twistedTransition_aux π w ppF cl a u va hw₁ hπ hva)
        (twistedTransition_aux π w ppS cl b u vb hw₂ hπ hvb) ψ =
      twistedComparison ell π η a b t va vb ha hb hva hvb

section Chart

variable {Y V : AlgebraicSpaces B S hS} (p : X ⟶ Y) (cm : V ⟶ Y) (πk : W ⟶ V) (u : V ⟶ U)
  (w : W ⟶ Y) (hw₁ : ell ≫ p = w) (hw₂ : πk ≫ cm = w) (hu : πk ≫ u = π)
  {M : Modules.{u, u} B S hS Y.1 Y.2}
  (α : (modulePullback B S hS cm).obj M ≅ (modulePullback B S hS u).obj G)

/-- The identification of `ell^*(p^*M)` with `π^*G` through a chart: `ell^*(p^*M)` and
`πk^*(cm^*M)` are both identified with `w^*M`, and `α : cm^*M ≅ u^*G` carries the second to
`πk^*(u^*G) = π^*G`. -/
noncomputable def chartIso :
    (modulePullback B S hS ell).obj ((modulePullback B S hS p).obj M) ≅
      (modulePullback B S hS π).obj G :=
  (pullbackComparison B S hS ell p w hw₁ M).symm ≪≫ pullbackComparison B S hS πk cm w hw₂ M ≪≫
    (modulePullback B S hS πk).mapIso α ≪≫ (pullbackComparison B S hS πk u π hu G).symm

/-- The inverse morphism of `chartIso` as a composite of pullback comparisons and the pullback of
`α.inv`. -/
theorem chartIso_inv :
    (chartIso ell π p cm πk u w hw₁ hw₂ hu α).inv =
      (pullbackComparison B S hS πk u π hu G).hom ≫ (modulePullback B S hS πk).map α.inv ≫
        (pullbackComparison B S hS πk cm w hw₂ M).inv ≫
          (pullbackComparison B S hS ell p w hw₁ M).hom := by
  simp [chartIso]

/-- The forward morphism of `chartIso` as a composite of pullback comparisons and the pullback of
`α.hom`. -/
theorem chartIso_hom :
    (chartIso ell π p cm πk u w hw₁ hw₂ hu α).hom =
      (pullbackComparison B S hS ell p w hw₁ M).inv ≫
        (pullbackComparison B S hS πk cm w hw₂ M).hom ≫ (modulePullback B S hS πk).map α.hom ≫
          (pullbackComparison B S hS πk u π hu G).inv := by
  simp [chartIso]

/-- Composing through `e` and `p` agrees with composing with `w = e ≫ p`. -/
private theorem comp_eq_of_comp_comp {C : Type*} [Category C] {T W X Y : C} {a : T ⟶ W}
    {e : W ⟶ X} {t : T ⟶ X} {t' : T ⟶ Y} {p : X ⟶ Y} {w : W ⟶ Y} (hw : e ≫ p = w)
    (ha : a ≫ e = t) (ht : t ≫ p = t') : a ≫ w = t' := by
  rw [← hw, ← Category.assoc, ha, ht]

/-- The restriction of the inverse of `chartIso`. -/
theorem moduleHomRestrict₂_chartIso_inv {T : AlgebraicSpaces B S hS} (a : T ⟶ W) (t : T ⟶ X)
    (va : T ⟶ U) (ha : a ≫ ell = t) (hva : a ≫ π = va) (c : T ⟶ V) (hc : a ≫ πk = c)
    (t' : T ⟶ Y) (ht' : t ≫ p = t') (hc' : c ≫ cm = t') (hcv : c ≫ u = va) :
    moduleHomRestrict₂ G ((modulePullback B S hS p).obj M) a π ell va t hva ha
        (chartIso ell π p cm πk u w hw₁ hw₂ hu α).inv =
      moduleHomRestrict₂ G M c u cm va t' hcv hc' α.inv ≫
        (pullbackComparison B S hS t p t' ht' M).hom := by
  have haw := comp_eq_of_comp_comp hw₁ ha ht'
  rw [chartIso_inv, moduleHomRestrict₂_comp a π πk ell va c t hva hc ha,
    moduleHomRestrict₂_comp a πk πk ell c c t hc hc ha,
    moduleHomRestrict₂_comp a πk w ell c t' t hc haw ha,
    moduleHomRestrict₂_pullbackComparison_hom πk u π hu a c hc va hva hcv,
    moduleHomRestrict₂_map a πk c hc α.inv,
    moduleHomRestrict₂_pullbackComparison_inv πk cm w hw₂ a c hc t' haw hc',
    moduleHomRestrict₂_pullbackComparison_hom ell p w hw₁ a t ha t' haw ht']
  simp only [moduleHomRestrict₂, Category.assoc]

/-- The restriction of `chartIso`. -/
theorem moduleHomRestrict₂_chartIso_hom {T : AlgebraicSpaces B S hS} (b : T ⟶ W) (t : T ⟶ X)
    (vb : T ⟶ U) (hb : b ≫ ell = t) (hvb : b ≫ π = vb) (d : T ⟶ V) (hd : b ≫ πk = d)
    (t' : T ⟶ Y) (ht' : t ≫ p = t') (hd' : d ≫ cm = t') (hdv : d ≫ u = vb) :
    moduleHomRestrict₂ ((modulePullback B S hS p).obj M) G b ell π t vb hb hvb
        (chartIso ell π p cm πk u w hw₁ hw₂ hu α).hom =
      (pullbackComparison B S hS t p t' ht' M).inv ≫
        moduleHomRestrict₂ M G d cm u t' vb hd' hdv α.hom := by
  have hbw := comp_eq_of_comp_comp hw₁ hb ht'
  rw [chartIso_hom, moduleHomRestrict₂_comp b ell w π t t' vb hb hbw hvb,
    moduleHomRestrict₂_comp b w πk π t' d vb hbw hd hvb,
    moduleHomRestrict₂_comp b πk πk π d d vb hd hd hvb,
    moduleHomRestrict₂_pullbackComparison_inv ell p w hw₁ b t hb t' hbw ht',
    moduleHomRestrict₂_pullbackComparison_hom πk cm w hw₂ b d hd t' hbw hd',
    moduleHomRestrict₂_map b πk d hd α.hom,
    moduleHomRestrict₂_pullbackComparison_inv πk u π hu b d hd vb hvb hdv]
  simp only [moduleHomRestrict₂]

/-- **The twisted comparison of an identification through a chart is the twisted comparison on
the chart.** -/
theorem twistedComparison_chartIso {T : AlgebraicSpaces B S hS} (a b : T ⟶ W) (t : T ⟶ X)
    (va vb : T ⟶ U) (ha : a ≫ ell = t) (hb : b ≫ ell = t) (hva : a ≫ π = va)
    (hvb : b ≫ π = vb) (c d : T ⟶ V) (hc : a ≫ πk = c) (hd : b ≫ πk = d) (t' : T ⟶ Y)
    (ht' : t ≫ p = t') (hc' : c ≫ cm = t') (hd' : d ≫ cm = t') (hcv : c ≫ u = va)
    (hdv : d ≫ u = vb) :
    twistedComparison ell π (chartIso ell π p cm πk u w hw₁ hw₂ hu α) a b t va vb ha hb hva hvb =
      twistedComparison cm u α c d t' va vb hc' hd' hcv hdv := by
  rw [twistedComparison,
    moduleHomRestrict₂_chartIso_inv ell π p cm πk u w hw₁ hw₂ hu α a t va ha hva c hc t' ht' hc'
      hcv,
    moduleHomRestrict₂_chartIso_hom ell π p cm πk u w hw₁ hw₂ hu α b t vb hb hvb d hd t' ht' hd'
      hdv,
    Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end Chart

end AlgebraicGeometry.Space

end
