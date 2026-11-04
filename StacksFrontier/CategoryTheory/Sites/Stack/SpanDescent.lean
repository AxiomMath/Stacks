module

public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.DescentDatum

/-!
# Descent in a category fibred in groupoids, read through spans

Let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids over a site `(𝒞, J)` and let
`{f i : V i ⟶ U}` be a covering family with chosen fibre products `V i ×_U V j` and
`V i ×_U V j ×_U V k`. A descent datum `CategoryTheory.Functor.DescentDatum` of Stacks 02ZC is
phrased through restrictions and gluing isomorphisms between them. Because every morphism of `𝒮`
is strongly cartesian, the same information is carried by *spans*: an object `e i j` over each
double overlap with a morphism `a i j : e i j ⟶ x i` over the first projection and a morphism
`b i j : e i j ⟶ x j` over the second, the gluing isomorphism being the comparison of the two
restrictions of `e i j` they exhibit. The cocycle condition becomes the existence, over each
triple overlap, of an object `t` mapping to the three spans compatibly. Effectivity becomes the
existence of an object `x₀` over `U` with morphisms `χ i : x i ⟶ x₀` over `f i` satisfying
`a i j ≫ χ i = b i j ≫ χ j`, a *cocone* on the spans.

This file proves the three translations. The span form is what a construction which descends the
components of a structured object separately can produce and consume: a functor over the base
carries spans and cocones to spans and cocones, whereas it carries a descent datum to one only
through a transport of its restrictions and of their canonical comparisons.

## Main results

* `CategoryTheory.Functor.DescentDatum.exists_span_cocycle`: the spans of a descent datum satisfy
  the span form of the cocycle condition.
* `CategoryTheory.Functor.DescentDatum.isEffective_of_cocone`: a cocone on the spans of a descent
  datum makes it effective.
* `CategoryTheory.Functor.IsStackInGroupoids.exists_cocone`: in a stack in groupoids every
  family of spans satisfying the span form of the cocycle condition has a cocone.

## References

* [Stacks Project, Tag 02ZC](https://stacks.math.columbia.edu/tag/02ZC)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ 𝒞}

/-- In a category fibred in groupoids every morphism lying over `f` is a restriction of its
target along `f`, every morphism being strongly cartesian. -/
noncomputable abbrev Restriction.ofIsHomLift (hp : p.IsFiberedInGroupoids) {V U : 𝒞} {f : V ⟶ U}
    {a x : 𝒮} (ha : p.obj a = V) (hx : p.obj x = U) (φ : a ⟶ x) (hφ : p.IsHomLift f φ) :
    Restriction p f x hx where
  pt := a
  hpt := ha
  hom := φ
  isHomLift := isHomLift_eqToHom ha hx hφ
  isCart := isStronglyCartesian_eqToHom ha hx (have := hφ; hp.isStronglyCartesian_homLift f φ)

/-- A morphism of the fibre category over `V` lies over the identity of `V`. -/
theorem FibreHom.isHomLift_id {V : 𝒞} {a b : 𝒮} {ha : p.obj a = V} {hb : p.obj b = V}
    {φ : a ⟶ b} (hφ : FibreHom p a b ha hb φ) : p.IsHomLift (𝟙 V) φ := by
  refine IsHomLift.of_fac' p (𝟙 V) φ ha hb ?_
  simpa using IsHomLift.fac' p (eqToHom ha ≫ eqToHom hb.symm) φ

/-- A morphism lying over an identity, followed by a morphism lying over `g`, lies over `g`. -/
private theorem isHomLift_comp_of_isHomLift_id {V W : 𝒞} {a b c : 𝒮} {φ : a ⟶ b}
    (hφ : p.IsHomLift (𝟙 V) φ) {g : V ⟶ W} {ψ : b ⟶ c} (hψ : p.IsHomLift g ψ) :
    p.IsHomLift g (φ ≫ ψ) := by
  have := hφ
  have := hψ
  simpa using (inferInstance : p.IsHomLift (𝟙 V ≫ g) (φ ≫ ψ))

/-- A morphism of a fibre followed by a morphism lying over `g` lies over `g`. -/
theorem FibreHom.isHomLift_comp {V W : 𝒞} {a b c : 𝒮} {ha : p.obj a = V} {hb : p.obj b = V}
    {φ : a ⟶ b} (hφ : FibreHom p a b ha hb φ) {g : V ⟶ W} {ψ : b ⟶ c}
    (hψ : p.IsHomLift g ψ) : p.IsHomLift g (φ ≫ ψ) :=
  isHomLift_comp_of_isHomLift_id hφ.isHomLift_id hψ

/-- The inverse of an invertible morphism of a fibre lies over the identity. -/
theorem FibreHom.isHomLift_inv {V : 𝒞} {a b : 𝒮} {ha : p.obj a = V} {hb : p.obj b = V}
    {φ : a ⟶ b} (hφ : FibreHom p a b ha hb φ) [IsIso φ] :
    p.IsHomLift (𝟙 V) (CategoryTheory.inv φ) := by
  have := hφ.isHomLift_id
  simpa using (inferInstance : p.IsHomLift (CategoryTheory.inv (𝟙 V)) (CategoryTheory.inv φ))

/-- Two lifts `u`, `v` of `g` factoring the cartesian morphisms of restrictions through those of
their restrictions along `g` exhibit `β` as the restriction of `α` once `β ≫ v = u ≫ α`. -/
private theorem isRestrictionOf_of_fac {W V Ux Uy : 𝒞} {g : W ⟶ V} {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    {mx : W ⟶ Ux} {my : W ⟶ Uy} {hmx : mx = g ≫ fx} {hmy : my = g ≫ fy} {x y : 𝒮}
    {hx : p.obj x = Ux} {hy : p.obj y = Uy} {xr : Restriction p fx x hx}
    {yr : Restriction p fy y hy} {xrW : Restriction p mx x hx} {yrW : Restriction p my y hy}
    {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt} (u : xrW.pt ⟶ xr.pt) (v : yrW.pt ⟶ yr.pt)
    (hu : p.IsHomLift g u) (hv : p.IsHomLift g v) (hux : u ≫ xr.hom = xrW.hom)
    (hvy : v ≫ yr.hom = yrW.hom) (h : β ≫ v = u ≫ α) :
    IsRestrictionOf p g hmx hmy xr yr xrW yrW α β := by
  rw [IsRestrictionOf, ← Restriction.eq_compTo g fx hmx xr xrW u hu hux,
    ← Restriction.eq_compTo g fy hmy yr yrW v hv hvy]
  exact h

section Span

variable {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → 𝒞}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- **The span form of the cocycle condition of a descent datum.** Over each triple overlap
there is an object `t` with morphisms `u`, `v`, `w` to the spans of the three double overlaps,
lying over the three projections, such that the composites to `x i`, `x j` and `x k` agree.

The spans of `D` are `(D.xrij i j).pt` with the morphisms `(D.xrij i j).hom` and
`D.φ i j ≫ (D.xrji i j).hom`. The object `t` is the restriction `D.wi i j k` of `x i` to the
triple overlap; the three identities are the three compatibilities `D.αij_restr`, `D.αjk_restr`
and `D.αik_restr` of the gluing isomorphisms with their restrictions, and the cocycle condition
`D.cocycle`. -/
theorem DescentDatum.exists_span_cocycle [p.IsFibered]
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (i j k : I) :
    ∃ (t : 𝒮) (_ : p.obj t = Vijk i j k) (s : Vijk i j k ⟶ Vij i k)
      (u : t ⟶ (D.xrij i j).pt) (v : t ⟶ (D.xrij j k).pt) (w : t ⟶ (D.xrij i k).pt),
      s ≫ pr₁ i k = s₁₂ i j k ≫ pr₁ i j ∧ s ≫ pr₂ i k = s₂₃ i j k ≫ pr₂ j k ∧
      p.IsHomLift (s₁₂ i j k) u ∧ p.IsHomLift (s₂₃ i j k) v ∧ p.IsHomLift s w ∧
      u ≫ D.φ i j ≫ (D.xrji i j).hom = v ≫ (D.xrij j k).hom ∧
      w ≫ (D.xrij i k).hom = u ≫ (D.xrij i j).hom ∧
      w ≫ D.φ i k ≫ (D.xrji i k).hom = v ≫ D.φ j k ≫ (D.xrji j k).hom := by
  have hαij := D.αij_restr i j k
  have hαjk := D.αjk_restr i j k
  have hαik := D.αik_restr i j k
  simp only [IsRestrictionOf] at hαij hαjk hαik
  refine ⟨(D.wi i j k).pt, (D.wi i j k).hpt, D.s₁₃ i j k,
    Restriction.compTo p (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (D.xrij i j) (D.wi i j k),
    D.αij i j k ≫ Restriction.compTo p (s₂₃ i j k) (pr₁ j k) ((hq₂ i j k).trans (hVijk i j k).w)
      (D.xrij j k) (D.wj i j k),
    Restriction.compTo p (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm (D.xrij i k) (D.wi i j k),
    (D.hs₁₃₁ i j k).trans (hq₁ i j k), (D.hs₁₃₂ i j k).trans (hq₃ i j k),
    Restriction.isHomLift_compTo _ _ _ _ _, ?_, Restriction.isHomLift_compTo _ _ _ _ _, ?_, ?_, ?_⟩
  · exact isHomLift_comp_of_isHomLift_id (D.isHomLift_id_αij i j k).1
      (Restriction.isHomLift_compTo _ _ _ _ _)
  · rw [← Category.assoc, ← hαij, Category.assoc, Restriction.compTo_hom, Category.assoc,
      Restriction.compTo_hom]
  · rw [Restriction.compTo_hom, Restriction.compTo_hom]
  · rw [← Category.assoc, ← hαik, Category.assoc, Restriction.compTo_hom, Category.assoc,
      ← Category.assoc _ (D.φ j k), ← hαjk, Category.assoc, Restriction.compTo_hom,
      ← Category.assoc, ← D.cocycle]

/-- **A cocone on the spans of a descent datum makes it effective.** If `χ i : x i ⟶ x₀` lie over
`f i` and agree on the spans of `D`, then `D` is effective: the restriction of `x₀` along `f i` is
`χ i` itself, read as a restriction, and the comparison with `x i` is the identity. -/
theorem DescentDatum.isEffective_of_cocone (hp : p.IsFiberedInGroupoids)
    (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (x₀ : 𝒮) (hx₀ : p.obj x₀ = U) (χ : ∀ i, D.x i ⟶ x₀) (hχ : ∀ i, p.IsHomLift (f i) (χ i))
    (hcone : ∀ i j, (D.xrij i j).hom ≫ χ i = (D.φ i j ≫ (D.xrji i j).hom) ≫ χ j) :
    D.IsEffective := by
  refine ⟨x₀, hx₀, fun i => Restriction.ofIsHomLift hp (D.hx i) hx₀ (χ i) (hχ i),
    fun i => 𝟙 (D.x i), fun i => FibreHom.id p _ _, fun i => IsIso.id _, fun i j => ?_⟩
  have hl : p.IsHomLift (pr₁ i j ≫ f i) ((D.xrij i j).hom ≫ χ i) := by
    have := (D.xrij i j).isHomLift_hom
    have := hχ i
    infer_instance
  refine ⟨Restriction.ofIsHomLift hp (D.xrij i j).hpt hx₀ _ hl, 𝟙 _, D.φ i j,
    FibreHom.id p _ _, D.φ_fibreHom i j, IsIso.id _, D.φ_iso i j, ?_, ?_, Category.id_comp _⟩
  · simp only [IsRestrictionOf, Category.id_comp, Category.comp_id]
    rw [← Restriction.eq_compTo _ _ _ _ _ (D.xrij i j).hom (D.xrij i j).isHomLift_hom
        (Category.comp_id _),
      ← Restriction.eq_compTo _ _ _ _ _ (D.xrij i j).hom (D.xrij i j).isHomLift_hom rfl]
  · simp only [IsRestrictionOf, Category.comp_id]
    have hb : p.IsHomLift (pr₂ i j) (D.φ i j ≫ (D.xrji i j).hom) :=
      (D.φ_fibreHom i j).isHomLift_comp (D.xrji i j).isHomLift_hom
    rw [← Restriction.eq_compTo _ _ _ _ _ (D.xrji i j).hom (D.xrji i j).isHomLift_hom
      (Category.comp_id _)]
    exact Restriction.eq_compTo (pr₂ i j) (f j) (hVij i j).w
      (Restriction.ofIsHomLift hp (D.hx j) hx₀ (χ j) (hχ j))
      (Restriction.ofIsHomLift hp (D.xrij i j).hpt hx₀ _ hl) _ hb (hcone i j).symm

end Span

/-- **In a stack in groupoids, spans satisfying the cocycle condition have a cocone.** Let
`{f i : V i ⟶ U}` be a covering family with genuine double and triple overlaps, let `x i` lie over
`V i`, and let `a i j : e i j ⟶ x i`, `b i j : e i j ⟶ x j` be spans over the two projections of
the double overlap satisfying the span form of the cocycle condition. Then there are an object
`x₀` over `U` and morphisms `χ i : x i ⟶ x₀` over `f i` agreeing on the spans.

The spans are a descent datum whose gluing isomorphisms are identities: the two restrictions of
the double overlap are `a i j` and `b i j`, with the common source `e i j`, and those of the triple
overlap are three composites with the common source `t`. Effectivity of that datum gives the
cocone. -/
theorem IsStackInGroupoids.exists_cocone {J : GrothendieckTopology 𝒞}
    (hp : p.IsStackInGroupoids.{w} J) {U : 𝒞} {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (Vijk : I → I → I → 𝒞)
    (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
    (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
    (x : I → 𝒮) (hx : ∀ i, p.obj (x i) = V i)
    (e : I → I → 𝒮) (he : ∀ i j, p.obj (e i j) = Vij i j)
    (a : ∀ i j, e i j ⟶ x i) (b : ∀ i j, e i j ⟶ x j)
    (ha : ∀ i j, p.IsHomLift (pr₁ i j) (a i j)) (hb : ∀ i j, p.IsHomLift (pr₂ i j) (b i j))
    (hcoc : ∀ i j k, ∃ (t : 𝒮) (_ : p.obj t = Vijk i j k) (s : Vijk i j k ⟶ Vij i k)
      (u : t ⟶ e i j) (v : t ⟶ e j k) (w : t ⟶ e i k),
      s ≫ pr₁ i k = s₁₂ i j k ≫ pr₁ i j ∧ s ≫ pr₂ i k = s₂₃ i j k ≫ pr₂ j k ∧
      p.IsHomLift (s₁₂ i j k) u ∧ p.IsHomLift (s₂₃ i j k) v ∧ p.IsHomLift s w ∧
      u ≫ b i j = v ≫ a j k ∧ w ≫ a i k = u ≫ a i j ∧ w ≫ b i k = v ≫ b j k) :
    ∃ (x₀ : 𝒮) (_ : p.obj x₀ = U) (χ : ∀ i, x i ⟶ x₀),
      (∀ i, p.IsHomLift (f i) (χ i)) ∧ ∀ i j, a i j ≫ χ i = b i j ≫ χ j := by
  have hfib := hp.isFiberedInGroupoids
  choose t ht s u v w hs₁ hs₂ hu hv hw huv hwa hwb using hcoc
  let xr₁ : ∀ i j, Restriction p (pr₁ i j) (x i) (hx i) := fun i j =>
    Restriction.ofIsHomLift hfib (he i j) (hx i) (a i j) (ha i j)
  let xr₂ : ∀ i j, Restriction p (pr₂ i j) (x j) (hx j) := fun i j =>
    Restriction.ofIsHomLift hfib (he i j) (hx j) (b i j) (hb i j)
  have hli : ∀ i j k, p.IsHomLift (s₁₂ i j k ≫ pr₁ i j) (u i j k ≫ a i j) := fun i j k => by
    have := hu i j k; have := ha i j; infer_instance
  have hlj : ∀ i j k, p.IsHomLift (s₁₂ i j k ≫ pr₂ i j) (v i j k ≫ a j k) := fun i j k => by
    have := hv i j k; have := ha j k
    rw [(hVijk i j k).w]; infer_instance
  have hlk : ∀ i j k, p.IsHomLift (s₂₃ i j k ≫ pr₂ j k) (v i j k ≫ b j k) := fun i j k => by
    have := hv i j k; have := hb j k; infer_instance
  let D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      (fun i j k => s₁₂ i j k ≫ pr₁ i j) (fun i j k => s₁₂ i j k ≫ pr₂ i j)
      (fun i j k => s₂₃ i j k ≫ pr₂ j k) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) :=
    { x := x
      hx := hx
      xrij := xr₁
      xrji := xr₂
      φ := fun i j => 𝟙 (e i j)
      φ_fibreHom := fun i j => FibreHom.id p _ _
      φ_iso := fun i j => inferInstance
      wi := fun i j k => Restriction.ofIsHomLift hfib (ht i j k) (hx i) _ (hli i j k)
      wj := fun i j k => Restriction.ofIsHomLift hfib (ht i j k) (hx j) _ (hlj i j k)
      wk := fun i j k => Restriction.ofIsHomLift hfib (ht i j k) (hx k) _ (hlk i j k)
      αij := fun i j k => 𝟙 (t i j k)
      αjk := fun i j k => 𝟙 (t i j k)
      αik := fun i j k => 𝟙 (t i j k)
      αij_restr := fun i j k => isRestrictionOf_of_fac (u i j k) (u i j k) (hu i j k) (hu i j k)
        rfl (huv i j k) ((Category.id_comp _).trans (Category.comp_id _).symm)
      αjk_restr := fun i j k => isRestrictionOf_of_fac (v i j k) (v i j k) (hv i j k) (hv i j k)
        rfl rfl ((Category.id_comp _).trans (Category.comp_id _).symm)
      s₁₃ := s
      hs₁₃₁ := hs₁
      hs₁₃₂ := hs₂
      αik_restr := fun i j k => isRestrictionOf_of_fac (w i j k) (w i j k) (hw i j k) (hw i j k)
        (hwa i j k) (hwb i j k) ((Category.id_comp _).trans (Category.comp_id _).symm)
      cocycle := fun i j k => (Category.comp_id _).symm }
  obtain ⟨x₀, hx₀, xr, ψ, hψ, hψiso, hcompat⟩ :=
    hp.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk _ _ _ _ _ _ D
  refine ⟨x₀, hx₀, fun i => CategoryTheory.inv (ψ i) ≫ (xr i).hom, fun i => ?_, fun i j => ?_⟩
  · exact isHomLift_comp_of_isHomLift_id (hψ i).isHomLift_inv (xr i).isHomLift_hom
  · obtain ⟨xr', ψ₁, ψ₂, -, -, hψ₁, hψ₂, h₁, h₂, h₁₂⟩ := hcompat i j
    simp only [IsRestrictionOf] at h₁ h₂
    rw [← Restriction.eq_compTo _ _ _ _ _ (a i j) (ha i j) (Category.comp_id _)] at h₁
    rw [← Restriction.eq_compTo _ _ _ _ _ (b i j) (hb i j) (Category.comp_id _)] at h₂
    change ψ₁ ≫ 𝟙 _ = ψ₂ at h₁₂
    rw [Category.comp_id] at h₁₂
    subst h₁₂
    dsimp only
    rw [← cancel_epi ψ₁, ← Category.assoc ψ₁ (a i j), h₁, ← Category.assoc ψ₁ (b i j), h₂]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, Restriction.compTo_hom]

/-- **In a stack in groupoids, a morphism is glued from a cocone over a covering family.** Let
`a i : t i ⟶ x` lie over a covering family `{f i : V i ⟶ U}` and `b i : t i ⟶ y` over the
composites `f i ≫ q`, both agreeing on spans `c i j`, `e i j` over the double overlaps. Then there
is a morphism `φ : x ⟶ y` over `q` with `a i ≫ φ = b i`.

The morphisms `b i` factor through a restriction of `y` along `q`, and the factorizations are
glued to a morphism of the fibre over `U` by the sheaf condition for `Isom`; the gluing family is
the family of identities of the `t i`. -/
theorem IsStackInGroupoids.exists_hom_of_cocone {J : GrothendieckTopology 𝒞}
    (hp : p.IsStackInGroupoids.{w} J) {U : 𝒞} {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → 𝒞) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    {T : 𝒞} (q : U ⟶ T) (x y : 𝒮) (hx : p.obj x = U) (hy : p.obj y = T)
    (t : I → 𝒮) (ht : ∀ i, p.obj (t i) = V i) (a : ∀ i, t i ⟶ x) (b : ∀ i, t i ⟶ y)
    (ha : ∀ i, p.IsHomLift (f i) (a i)) (hb : ∀ i, p.IsHomLift (f i ≫ q) (b i))
    (e : I → I → 𝒮) (he : ∀ i j, p.obj (e i j) = Vij i j)
    (c : ∀ i j, e i j ⟶ t i) (c' : ∀ i j, e i j ⟶ t j)
    (hc : ∀ i j, p.IsHomLift (pr₁ i j) (c i j)) (hc' : ∀ i j, p.IsHomLift (pr₂ i j) (c' i j))
    (hca : ∀ i j, c i j ≫ a i = c' i j ≫ a j) (hcb : ∀ i j, c i j ≫ b i = c' i j ≫ b j) :
    ∃ φ : x ⟶ y, p.IsHomLift q φ ∧ ∀ i, a i ≫ φ = b i := by
  have hfib := hp.isFiberedInGroupoids
  have := hfib.isFibered
  let r := Restriction.ofIsFiberedInGroupoids p hfib q y hy
  let br : ∀ i, Restriction p (f i ≫ q) y hy := fun i =>
    Restriction.ofIsHomLift hfib (ht i) hy (b i) (hb i)
  let β : ∀ i, t i ⟶ r.pt := fun i => Restriction.compTo p (f i) q rfl r (br i)
  have hβ : ∀ i, p.IsHomLift (f i) (β i) := fun i => Restriction.isHomLift_compTo _ _ _ _ _
  have hβfac : ∀ i, β i ≫ r.hom = b i := fun i => Restriction.compTo_hom p _ _ _ r (br i)
  have hβc : ∀ i j, c i j ≫ β i = c' i j ≫ β j := by
    intro i j
    have := r.isStronglyCartesian_hom
    have := hc i j; have := hc' i j; have := hβ i; have := hβ j
    have h₂ : p.IsHomLift (pr₁ i j ≫ f i) (c' i j ≫ β j) := by
      rw [(hVij i j).w]; infer_instance
    refine IsStronglyCartesian.ext p q r.hom (pr₁ i j ≫ f i) ?_
    rw [Category.assoc, Category.assoc, hβfac, hβfac, hcb]
  have hl₁ : ∀ i j, p.IsHomLift (pr₁ i j ≫ f i) (c i j ≫ a i) := fun i j => by
    have := hc i j; have := ha i; infer_instance
  have hl₂ : ∀ i j, p.IsHomLift (pr₁ i j ≫ f i) (c i j ≫ β i) := fun i j => by
    have := hc i j; have := hβ i; infer_instance
  let xr : ∀ i, Restriction p (f i) x hx := fun i =>
    Restriction.ofIsHomLift hfib (ht i) hx (a i) (ha i)
  let yr : ∀ i, Restriction p (f i) r.pt r.hpt := fun i =>
    Restriction.ofIsHomLift hfib (ht i) r.hpt (β i) (hβ i)
  let xrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) x hx := fun i j =>
    Restriction.ofIsHomLift hfib (he i j) hx _ (hl₁ i j)
  let yrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) r.pt r.hpt := fun i j =>
    Restriction.ofIsHomLift hfib (he i j) r.hpt _ (hl₂ i j)
  obtain ⟨g, ⟨hg, -, hga⟩, -⟩ := hp.isom_isSheaf x r.pt hx r.hpt V f hf Vij pr₁ pr₂ hVij
    xr yr xrij yrij (fun i => 𝟙 (t i)) (fun i => FibreHom.id p _ _) (fun i => IsIso.id _)
    (fun i j => ⟨𝟙 (e i j), FibreHom.id p _ _,
      isRestrictionOf_of_fac (c i j) (c i j) (hc i j) (hc i j) rfl rfl
        ((Category.id_comp _).trans (Category.comp_id _).symm),
      isRestrictionOf_of_fac (c' i j) (c' i j) (hc' i j) (hc' i j) (hca i j).symm
        (hβc i j).symm ((Category.id_comp _).trans (Category.comp_id _).symm)⟩)
  refine ⟨g ≫ r.hom, ?_, fun i => ?_⟩
  · exact hg.isHomLift_comp r.isHomLift_hom
  · rw [← Category.assoc, show a i ≫ g = β i from (hga i).trans (Category.id_comp _), hβfac]

section FullSubcategory

variable (P : ObjectProperty 𝒮)

/-- A restriction in a full subcategory, read in the ambient category. -/
noncomputable abbrev Restriction.toAmbient (hp : p.IsFiberedInGroupoids) {V U : 𝒞} {f : V ⟶ U}
    {x : P.FullSubcategory} {hx : (P.ι ⋙ p).obj x = U} (r : Restriction (P.ι ⋙ p) f x hx) :
    Restriction p f x.obj hx :=
  Restriction.ofIsHomLift hp r.hpt hx r.hom.hom
    ((isHomLift_comp_iff P.ι p f r.hom).1 r.isHomLift_hom)

/-- The canonical comparison of two restrictions in a full subcategory is the canonical
comparison of the two restrictions read in the ambient category. -/
theorem Restriction.compTo_toAmbient_hom (hp : p.IsFiberedInGroupoids)
    (hP : (P.ι ⋙ p).IsFiberedInGroupoids) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : P.FullSubcategory} {hx : (P.ι ⋙ p).obj x = U}
    (xr : Restriction (P.ι ⋙ p) f x hx) (xrW : Restriction (P.ι ⋙ p) h x hx) :
    (Restriction.compTo (P.ι ⋙ p) g f hh xr xrW).hom =
      Restriction.compTo p g f hh (xr.toAmbient P hp) (xrW.toAmbient P hp) := by
  have := hP.isFibered
  refine Restriction.eq_compTo g f hh (xr.toAmbient P hp) (xrW.toAmbient P hp) _
    ((isHomLift_comp_iff P.ι p g _).1 (Restriction.isHomLift_compTo _ _ _ _ _)) ?_
  exact congrArg InducedCategory.Hom.hom (Restriction.compTo_hom (P.ι ⋙ p) g f hh xr xrW)

/-- **Stacks in groupoids pass to full subcategories which are local.** Let `p` be a stack in
groupoids and `P` a property of its objects such that `P.ι ⋙ p` is fibred in groupoids — that is,
`P` is inherited by the source of every morphism into an object of `P`, up to the lifts that
exist — and such that an object over `U` has `P` as soon as it receives morphisms over the
members of a covering family from objects with `P`. Then `P.ι ⋙ p` is a stack in groupoids.

This is the covering-family form of Stacks 04TU: condition (1) is the fibred-in-groupoids
hypothesis, condition (2) holds because the subcategory is full, and condition (3) is `hloc`. -/
theorem IsStackInGroupoids.ι_comp {J : GrothendieckTopology 𝒞}
    (hp : p.IsStackInGroupoids.{w} J) (hP : (P.ι ⋙ p).IsFiberedInGroupoids)
    (hloc : ∀ {U : 𝒞} {I : Type w} (V : I → 𝒞) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U → ∀ (x₀ : 𝒮), p.obj x₀ = U → ∀ (x : I → 𝒮)
        (χ : ∀ i, x i ⟶ x₀), (∀ i, p.IsHomLift (f i) (χ i)) → (∀ i, P (x i)) → P x₀) :
    (P.ι ⋙ p).IsStackInGroupoids.{w} J where
  isFiberedInGroupoids := hP
  isom_isSheaf := by
    have hfib := hp.isFiberedInGroupoids
    intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij φ hφ hφiso hover
    have hφ' : ∀ i, FibreHom p (xr i).pt.obj (yr i).pt.obj (xr i).hpt (yr i).hpt (φ i).hom :=
      fun i => (isHomLift_comp_iff P.ι p _ _).1 (hφ i)
    have hφiso' : ∀ i, IsIso (φ i).hom := fun i =>
      have := hφiso i; inferInstanceAs (IsIso (P.ι.map (φ i)))
    obtain ⟨g, ⟨hgf, hgiso, hg⟩, hguniq⟩ := hp.isom_isSheaf x.obj y.obj hx hy V f hf Vij pr₁ pr₂
      hVij (fun i => (xr i).toAmbient P hfib) (fun i => (yr i).toAmbient P hfib)
      (fun i j => (xrij i j).toAmbient P hfib) (fun i j => (yrij i j).toAmbient P hfib)
      (fun i => (φ i).hom) hφ' hφiso' (fun i j => by
        obtain ⟨γ, hγ, h₁, h₂⟩ := hover i j
        refine ⟨γ.hom, (isHomLift_comp_iff P.ι p _ _).1 hγ, ?_, ?_⟩
        · have := congrArg InducedCategory.Hom.hom h₁
          simp only [ObjectProperty.FullSubcategory.comp_hom,
            Restriction.compTo_toAmbient_hom P hfib hP] at this
          exact this
        · have := congrArg InducedCategory.Hom.hom h₂
          simp only [ObjectProperty.FullSubcategory.comp_hom,
            Restriction.compTo_toAmbient_hom P hfib hP] at this
          exact this)
    have : IsIso (P.ι.map (ObjectProperty.homMk g)) := hgiso
    refine ⟨ObjectProperty.homMk g, ⟨(isHomLift_comp_iff P.ι p _ _).2 hgf,
      P.fullyFaithfulι.isIso_of_isIso_map _,
      fun i => InducedCategory.hom_ext (hg i)⟩, ?_⟩
    rintro g' ⟨hg'f, hg'iso, hg'⟩
    refine InducedCategory.hom_ext (hguniq g'.hom ⟨(isHomLift_comp_iff P.ι p _ _).1 hg'f,
      inferInstanceAs (IsIso (P.ι.map g')), fun i => congrArg InducedCategory.Hom.hom (hg' i)⟩)
  effective_descent := by
    have hfib := hp.isFiberedInGroupoids
    have := hP.isFibered
    intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    have hι : ∀ {R S : 𝒞} (f : R ⟶ S) {a b : P.FullSubcategory} (φ : a ⟶ b),
        (P.ι ⋙ p).IsHomLift f φ → p.IsHomLift f φ.hom :=
      fun {_ _} f {_ _} φ h => (isHomLift_comp_iff P.ι p f φ).1 h
    obtain ⟨x₀, hx₀, χ, hχ, hcone⟩ := hp.exists_cocone V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃
      hVijk (fun i => (D.x i).obj) D.hx (fun i j => (D.xrij i j).pt.obj)
      (fun i j => (D.xrij i j).hpt)
      (fun i j => (D.xrij i j).hom.hom) (fun i j => (D.φ i j ≫ (D.xrji i j).hom).hom)
      (fun i j => hι _ _ (D.xrij i j).isHomLift_hom)
      (fun i j => hι _ _ ((D.φ_fibreHom i j).isHomLift_comp (D.xrji i j).isHomLift_hom))
      (fun i j k => by
        obtain ⟨t, ht, s, u, v, w, hs₁, hs₂, hu, hv, hw, huv, hwa, hwb⟩ :=
          D.exists_span_cocycle i j k
        refine ⟨t.obj, ht, s, u.hom, v.hom, w.hom, hs₁, hs₂, hι _ _ hu, hι _ _ hv, hι _ _ hw,
          ?_, ?_, ?_⟩
        · simpa using congrArg InducedCategory.Hom.hom huv
        · simpa using congrArg InducedCategory.Hom.hom hwa
        · simpa using congrArg InducedCategory.Hom.hom hwb)
    have hP₀ : P x₀ := hloc V f hf x₀ hx₀ _ χ hχ fun i => (D.x i).property
    refine D.isEffective_of_cocone hP ⟨x₀, hP₀⟩ hx₀ (fun i => ObjectProperty.homMk (χ i))
      (fun i => (isHomLift_comp_iff P.ι p _ _).2 (hχ i)) fun i j => ?_
    exact InducedCategory.hom_ext (hcone i j)

end FullSubcategory

end CategoryTheory.Functor

end
