module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Cancelling the middle factor on the second side of a 2-fibre product (Stacks 02XD)

Fix a base category `𝒞` and categories `𝒵`, `𝒳`, `𝒴`, `𝒰` over `𝒞`, together with 1-morphisms
over `𝒞`

```text
g : 𝒵 ⥤ 𝒴,   f : 𝒳 ⥤ 𝒴,   c : 𝒰 ⥤ 𝒳
```

and a 1-morphism `G : 𝒰 ⥤ 𝒴` identified with `c ⋙ f` by a vertical 2-isomorphism `θ`. Writing
`×` for `CategoryTheory.TwoFibreProductOver`, there are two 2-fibre products in sight: the
iterated one `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`, formed over `𝒳` along the *second* projection of the inner
product, and `𝒵 ×_𝒴 𝒰`. This file constructs the canonical comparison

```text
(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰  ≃  𝒵 ×_𝒴 𝒰       over `𝒞`
```

and shows it is an equivalence. It is the over-a-base form of Stacks 02XD, whose plain form —
for Mathlib's `CategoryTheory.Limits.CategoricalPullback`, with no size or existence hypotheses —
is `CategoryTheory.Limits.CategoricalPullback.assocComp`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.cancelSnd`: the comparison functor, sending
  `((U, z, x, ψ), u, φ)` to `(U, z, u, θ_u ∘ f(φ) ∘ ψ)`.

## Main results

* `CategoryTheory.TwoFibreProductOver.cancelSnd_comp_structureFunctor`: the comparison is
  strictly over `𝒞`.
* `CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst`: it commutes with the projections to
  `𝒵` on the nose.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_cancelSnd`: it is an equivalence of
  categories.
* `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_cancelSnd`: hence an equivalence
  over `𝒞`, once both structure functors are fibred in groupoids.

## Implementation notes

The reindexing 2-isomorphism `θ` is carried rather than fixing `G = c ⋙ f`, because the
consumer compares two iterated products whose outer factors are different — `𝒵 ×_𝒴 𝒳` against
`𝒵 ×_𝒴 𝒱` for a second `𝒱` — and they only land in a *common* target `𝒵 ×_𝒴 𝒰` once the two
composites `c ⋙ f` are identified by the 2-cell of the square. With `θ = Iso.refl` the statement
is the bare cancellation.

The comparison is shown to be an equivalence by exhibiting it as full, faithful and essentially
surjective rather than by writing down a quasi-inverse, following
`CategoryTheory.TwoFibreProductOver.swap`. Faithfulness is the reason the statement is true at
all: a morphism of the iterated product has an `𝒳`-component, and the compatibility square of
the outer product determines that component from the `𝒰`-component, so nothing is lost by
forgetting it.

`cancelSnd` is built from its object and morphism parts as separate definitions so that the two
compatibilities above hold by `rfl`: both projections read off a field of the structure that
`cancelSndObj` and `cancelSndMap` write, and nothing is transported.

`attribute [local implicit_reducible]` on the four definitions in play is required, for the
reason recorded in `StacksFrontier/CategoryTheory/TwoFibreProduct/Cancellation.lean` for `π₂`:
Lean checks implicit arguments at `implicit` transparency, which unfolds only reducible
definitions, and objects of the iterated product have their comparison isomorphism typed through
`(snd …).obj`. Without it the goals of the fullness proof are not type-correct at that level and
`CategoryTheory.TwoFibreProductOver.Hom.w` cannot be rewritten — `simp` and `rw` then fail
silently rather than reporting a mismatch.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒵 : Type u₂} [Category.{v₂} 𝒵]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {𝒰 : Type u₅} [Category.{v₅} 𝒰]
  (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒰 : 𝒰 ⥤ 𝒞)
  (g : 𝒵 ⥤ 𝒴) (f : 𝒳 ⥤ 𝒴) (c : 𝒰 ⥤ 𝒳) (G : 𝒰 ⥤ 𝒴)
  (hf : f ⋙ p𝒴 = p𝒳) (hc : c ⋙ p𝒳 = p𝒰)
  (θ : c ⋙ f ≅ G) (hθ : ∀ u : 𝒰, p𝒴.IsHomLift (𝟙 (p𝒰.obj u)) (θ.hom.app u))

include hc in
/-- **The comparison of Stacks 02XD on objects.** An object `((U, z, x, ψ), u, φ)` of the
iterated 2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰` — so `ψ : g z ≅ f x` and `φ : x ≅ c u`, both
vertical over `U` — becomes the object `(U, z, u, θ_u ∘ f(φ) ∘ ψ)` of `𝒵 ×_𝒴 𝒰`. The `𝒳`-entry
is forgotten and its comparison absorbed into the new one. -/
def cancelSndObj
    (P : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c) :
    TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G where
  base := P.base
  x := P.x.x
  y := P.y
  hx := P.x.hx.trans (show P.x.base = P.base from P.hx)
  hy := P.hy
  iso := P.x.iso ≪≫ f.mapIso P.iso ≪≫ θ.app P.y
  vertical := by
    have hb : P.x.base = P.base := P.hx
    have h1 : p𝒴.IsHomLift (𝟙 P.base) P.x.iso.hom := by
      have h := P.x.vertical
      rwa [hb] at h
    have h2 : p𝒳.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have h3 : p𝒴.IsHomLift (𝟙 P.base) (f.map P.iso.hom) :=
      Functor.isHomLift_map_of_comp_eq hf (𝟙 P.base) P.iso.hom
    have h5 : p𝒴.IsHomLift (𝟙 P.base) (θ.hom.app P.y) := by
      have h := hθ P.y
      rwa [P.hy] at h
    change p𝒴.IsHomLift (𝟙 P.base) (P.x.iso.hom ≫ f.map P.iso.hom ≫ θ.hom.app P.y)
    exact @IsHomLift.comp_of_lift_id _ _ _ _ p𝒴 P.base _ _ _ P.x.iso.hom
      (f.map P.iso.hom ≫ θ.hom.app P.y) h1
      (@IsHomLift.comp_of_lift_id _ _ _ _ p𝒴 P.base _ _ _ (f.map P.iso.hom)
        (θ.hom.app P.y) h3 h5)

include hc in
/-- **The comparison of Stacks 02XD on morphisms.** A morphism of the iterated 2-fibre product
has a `𝒵`-component inside its `𝒵 ×_𝒴 𝒳`-component and a `𝒰`-component; those two are the
components of its image, over the same base morphism. -/
def cancelSndMap
    {P Q : TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c} (m : P ⟶ Q) :
    cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ P ⟶
      cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ Q where
  hbase := m.hbase
  a := m.a.a
  b := m.b
  ha := by
    have := m.ha
    have := m.a.ha
    have hPX : P.x.base = P.base := P.hx
    have hQX : Q.x.base = Q.base := Q.hx
    have h2 : m.a.hbase = eqToHom hPX ≫ m.hbase ≫ eqToHom hQX.symm :=
      IsHomLift.fac' (structureFunctor p𝒵 p𝒳 p𝒴 g f) m.hbase m.a
    have h1 : p𝒵.map m.a.a = eqToHom P.x.hx ≫ m.a.hbase ≫ eqToHom Q.x.hx.symm :=
      IsHomLift.fac' p𝒵 m.a.hbase m.a.a
    refine IsHomLift.of_fac' p𝒵 m.hbase m.a.a (P.x.hx.trans hPX) (Q.x.hx.trans hQX) ?_
    rw [h1, h2]
    simp
  hb := m.hb
  w := by
    have hma : g.map m.a.a ≫ Q.x.iso.hom = P.x.iso.hom ≫ f.map m.a.b := m.a.w
    have hmw : m.a.b ≫ Q.iso.hom = P.iso.hom ≫ c.map m.b := m.w
    have step : f.map m.a.b ≫ f.map Q.iso.hom = f.map P.iso.hom ≫ f.map (c.map m.b) :=
      (f.map_comp m.a.b Q.iso.hom).symm.trans
        ((congrArg f.map hmw).trans (f.map_comp P.iso.hom (c.map m.b)))
    have hnat : f.map (c.map m.b) ≫ θ.hom.app Q.y = θ.hom.app P.y ≫ G.map m.b :=
      θ.hom.naturality m.b
    have step2 : f.map m.a.b ≫ f.map Q.iso.hom ≫ θ.hom.app Q.y
        = f.map P.iso.hom ≫ θ.hom.app P.y ≫ G.map m.b :=
      ((Category.assoc (f.map m.a.b) (f.map Q.iso.hom) (θ.hom.app Q.y)).symm.trans
        (congrArg (· ≫ θ.hom.app Q.y) step)).trans
        ((Category.assoc (f.map P.iso.hom) (f.map (c.map m.b)) (θ.hom.app Q.y)).trans
          (congrArg (f.map P.iso.hom ≫ ·) hnat))
    have key : g.map m.a.a ≫ Q.x.iso.hom ≫ f.map Q.iso.hom ≫ θ.hom.app Q.y
        = (P.x.iso.hom ≫ f.map P.iso.hom ≫ θ.hom.app P.y) ≫ G.map m.b :=
      ((Category.assoc (g.map m.a.a) Q.x.iso.hom
          (f.map Q.iso.hom ≫ θ.hom.app Q.y)).symm.trans
        (congrArg (· ≫ f.map Q.iso.hom ≫ θ.hom.app Q.y) hma)).trans
        (((Category.assoc P.x.iso.hom (f.map m.a.b)
            (f.map Q.iso.hom ≫ θ.hom.app Q.y)).trans
          (congrArg (P.x.iso.hom ≫ ·) step2)).trans
          ((congrArg (P.x.iso.hom ≫ ·)
            (Category.assoc (f.map P.iso.hom) (θ.hom.app P.y) (G.map m.b)).symm).trans
            (Category.assoc P.x.iso.hom (f.map P.iso.hom ≫ θ.hom.app P.y)
              (G.map m.b)).symm))
    exact key

include hc in
/-- **The comparison functor of Stacks 02XD, over a base.** The canonical functor
`(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰 ⥤ 𝒵 ×_𝒴 𝒰` built from
`CategoryTheory.TwoFibreProductOver.cancelSndObj` and
`CategoryTheory.TwoFibreProductOver.cancelSndMap`. -/
def cancelSnd :
    TwoFibreProductOver (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
        (snd p𝒵 p𝒳 p𝒴 g f) c ⥤
      TwoFibreProductOver p𝒵 p𝒰 p𝒴 g G where
  obj P := cancelSndObj p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ P
  map m := cancelSndMap p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ m
  map_id P := by apply Hom.ext <;> rfl
  map_comp m n := by apply Hom.ext <;> rfl

/-- **The comparison is strictly over `𝒞`**: it changes neither the base object of an object nor
the base morphism of a morphism. -/
lemma cancelSnd_comp_structureFunctor :
    cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ ⋙ structureFunctor p𝒵 p𝒰 p𝒴 g G =
      structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c := rfl

/-- **The comparison commutes with the projections to `𝒵`** on the nose: the `𝒵`-entry of the
image of an object is the `𝒵`-entry of its inner `𝒵 ×_𝒴 𝒳`-component. This is what lets a
statement about the projection of `𝒵 ×_𝒴 𝒰` be read as one about the composite of the two
projections of the iterated product. -/
lemma cancelSnd_comp_fst :
    cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ ⋙ fst p𝒵 p𝒰 p𝒴 g G =
      fst (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c ⋙
        fst p𝒵 p𝒳 p𝒴 g f := rfl

/-- **The comparison is faithful.** A morphism of the iterated product is determined by the two
components the comparison keeps, because the compatibility square of the outer product expresses
its `𝒳`-component through its `𝒰`-component and the two comparison isomorphisms. -/
theorem faithful_cancelSnd : (cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ).Faithful where
  map_injective {P Q} {m m'} h := by
    have hb : m.b = m'.b := congrArg (·.b) h
    have haa : m.a.a = m'.a.a := congrArg (·.a) h
    refine Hom.ext' (Hom.ext' haa ?_) hb
    have h1 : m.a.b ≫ Q.iso.hom = P.iso.hom ≫ c.map m.b := m.w
    have h2 : m'.a.b ≫ Q.iso.hom = P.iso.hom ≫ c.map m'.b := m'.w
    rw [hb] at h1
    exact (cancel_mono Q.iso.hom).mp (h1.trans h2.symm)

attribute [local implicit_reducible] cancelSndObj cancelSnd snd structureFunctor

include hc in
/-- **The comparison is full.** The `𝒳`-component that the comparison forgets can be written
down: `φ_P ∘ c(b) ∘ φ_Q⁻¹` is the only candidate, and the compatibility square of the image
morphism says exactly that it makes both squares of the iterated product commute. -/
theorem full_cancelSnd : (cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ).Full where
  map_surjective {P Q} n := by
    have hnat : f.map (c.map n.b) ≫ θ.hom.app Q.y = θ.hom.app P.y ≫ G.map n.b :=
      θ.hom.naturality n.b
    have hnw : g.map n.a ≫ Q.x.iso.hom ≫ f.map Q.iso.hom ≫ θ.hom.app Q.y
        = (P.x.iso.hom ≫ f.map P.iso.hom ≫ θ.hom.app P.y) ≫ G.map n.b := n.w
    have hbig : (g.map n.a ≫ Q.x.iso.hom) ≫ (f.map Q.iso.hom ≫ θ.hom.app Q.y)
        = (P.x.iso.hom ≫ f.map (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv))
            ≫ (f.map Q.iso.hom ≫ θ.hom.app Q.y) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (f.map Q.iso.inv), ← f.map_comp, Iso.inv_hom_id, f.map_id,
        Category.id_comp, hnat]
      simpa only [Category.assoc] using hnw
    have hw : g.map n.a ≫ Q.x.iso.hom
        = P.x.iso.hom ≫ f.map (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv) :=
      (cancel_mono (f.map Q.iso.hom ≫ θ.hom.app Q.y)).mp hbig
    have hPiso : p𝒳.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have hQiso : p𝒳.IsHomLift (𝟙 Q.base) Q.iso.inv :=
      @IsHomLift.lift_id_inv _ _ _ _ p𝒳 Q.base _ _ Q.iso Q.vertical
    have hnb : p𝒰.IsHomLift n.hbase n.b := n.hb
    have hcn : p𝒳.IsHomLift n.hbase (c.map n.b) :=
      Functor.isHomLift_map_of_comp_eq hc n.hbase n.b
    have h2a : p𝒳.IsHomLift n.hbase (c.map n.b ≫ Q.iso.inv) :=
      @IsHomLift.comp_lift_id_right _ _ _ _ p𝒳 _ _ _ _ _ n.hbase (c.map n.b) hcn
        Q.iso.inv hQiso
    have h2 : p𝒳.IsHomLift n.hbase (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv) :=
      @IsHomLift.comp_lift_id_left _ _ _ _ p𝒳 _ _ _ _ _ n.hbase
        (c.map n.b ≫ Q.iso.inv) h2a P.iso.hom hPiso
    have hna : p𝒵.IsHomLift n.hbase n.a := n.ha
    have hfacA : p𝒵.map n.a
        = eqToHom (P.x.hx.trans (show P.x.base = P.base from P.hx)) ≫ n.hbase ≫
          eqToHom (Q.x.hx.trans (show Q.x.base = Q.base from Q.hx)).symm :=
      IsHomLift.fac' p𝒵 n.hbase n.a
    have hfacB : p𝒳.map (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv)
        = eqToHom (P.x.hy.trans (show P.x.base = P.base from P.hx)) ≫ n.hbase ≫
          eqToHom (Q.x.hy.trans (show Q.x.base = Q.base from Q.hx)).symm :=
      IsHomLift.fac' p𝒳 n.hbase _
    have hfacC : p𝒰.map n.b
        = eqToHom (show p𝒰.obj P.y = P.base from P.hy) ≫ n.hbase ≫
          eqToHom (show p𝒰.obj Q.y = Q.base from Q.hy).symm :=
      IsHomLift.fac' p𝒰 n.hbase n.b
    refine ⟨Hom.mk' (Hom.mk' n.a (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv) ?_ hw) n.b ?_ ?_, ?_⟩
    · rw [hfacA, hfacB]; simp
    · rw [hfacC]
      change _ = eqToHom _ ≫ (eqToHom P.x.hx.symm ≫ p𝒵.map n.a ≫ eqToHom Q.x.hx) ≫ eqToHom _
      rw [hfacA]; simp
    · change (P.iso.hom ≫ c.map n.b ≫ Q.iso.inv) ≫ Q.iso.hom = P.iso.hom ≫ c.map n.b
      simp
    · exact Hom.ext' rfl rfl

include hc in
/-- **The comparison is essentially surjective.** An object `(U, z, u, χ)` of `𝒵 ×_𝒴 𝒰` is the
image of `((U, z, c u, θ_u⁻¹ ∘ χ), u, 𝟙)`, up to the isomorphism that `f(𝟙) = 𝟙` and
`θ_u ∘ θ_u⁻¹ = 𝟙` provide. -/
theorem essSurj_cancelSnd : (cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ).EssSurj where
  mem_essImage Q := by
    have hcy : p𝒳.obj (c.obj Q.y) = Q.base := (Functor.congr_obj hc Q.y).trans Q.hy
    have hθQ : p𝒴.IsHomLift (𝟙 Q.base) (θ.hom.app Q.y) := Q.hy ▸ hθ Q.y
    have hθQinv : p𝒴.IsHomLift (𝟙 Q.base) (θ.app Q.y).inv :=
      @IsHomLift.lift_id_inv _ _ _ _ p𝒴 Q.base _ _ (θ.app Q.y) hθQ
    have hinner : p𝒴.IsHomLift (𝟙 Q.base) (Q.iso.hom ≫ (θ.app Q.y).inv) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ p𝒴 Q.base _ _ _ Q.iso.hom
        (θ.app Q.y).inv Q.vertical hθQinv
    have hid : p𝒳.IsHomLift (𝟙 Q.base) (𝟙 (c.obj Q.y)) := by
      rw [← hcy]
      infer_instance
    refine ⟨{ base := Q.base
              x := { base := Q.base, x := Q.x, y := c.obj Q.y, hx := Q.hx, hy := hcy
                     iso := Q.iso ≪≫ (θ.app Q.y).symm, vertical := hinner }
              y := Q.y
              hx := rfl
              hy := Q.hy
              iso := Iso.refl (c.obj Q.y)
              vertical := hid }, ⟨?_⟩⟩
    have hbase1 : eqToHom (show Q.base = p𝒰.obj Q.y from Q.hy.symm) ≫ p𝒰.map (𝟙 Q.y) ≫
          eqToHom (show p𝒰.obj Q.y = Q.base from Q.hy)
        = eqToHom (show Q.base = p𝒵.obj Q.x from Q.hx.symm) ≫ p𝒵.map (𝟙 Q.x) ≫
          eqToHom (show p𝒵.obj Q.x = Q.base from Q.hx) := by
      simp only [Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    have hw1 : g.map (𝟙 Q.x) ≫ Q.iso.hom
        = ((Q.iso.hom ≫ (θ.app Q.y).inv) ≫
            f.map (𝟙 (c.obj Q.y)) ≫ θ.hom.app Q.y) ≫ G.map (𝟙 Q.y) := by
      simp
    have hw2 : g.map (𝟙 Q.x) ≫ ((Q.iso.hom ≫ (θ.app Q.y).inv) ≫
          f.map (𝟙 (c.obj Q.y)) ≫ θ.hom.app Q.y)
        = Q.iso.hom ≫ G.map (𝟙 Q.y) := by
      simp
    exact { hom := Hom.mk' (𝟙 Q.x) (𝟙 Q.y) hbase1 hw1
            inv := Hom.mk' (𝟙 Q.x) (𝟙 Q.y) hbase1 hw2
            hom_inv_id := Hom.ext' (by simp; rfl) (by simp; rfl)
            inv_hom_id := Hom.ext' (by simp) (by simp) }

include hc in
/-- **The comparison of Stacks 02XD is an equivalence of categories.** -/
theorem isEquivalence_cancelSnd :
    (cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ).IsEquivalence :=
  have := faithful_cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ
  have := full_cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ
  have := essSurj_cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ
  Functor.IsEquivalence.mk

include hf hc θ hθ in
/-- **Stacks 02XD over a base.** The iterated 2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰` and
`𝒵 ×_𝒴 𝒰` are equivalent in the 2-category of categories over `𝒞`, as soon as both structure
functors are fibred in groupoids.

Only `Nonempty` is asserted, for the reason recorded at
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`: the quasi-inverse over `𝒞`
is produced by a choice inside an existential statement, and every consumer asks for no more. -/
theorem nonempty_equivalenceOver_cancelSnd
    (h₁ : (structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳
      (snd p𝒵 p𝒳 p𝒴 g f) c).IsFiberedInGroupoids)
    (h₂ : (structureFunctor p𝒵 p𝒰 p𝒴 g G).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (structureFunctor (structureFunctor p𝒵 p𝒳 p𝒴 g f) p𝒰 p𝒳 (snd p𝒵 p𝒳 p𝒴 g f) c)
      (structureFunctor p𝒵 p𝒰 p𝒴 g G)) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ)
    (cancelSnd_comp_structureFunctor p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf θ hθ)
    (isEquivalence_cancelSnd p𝒵 p𝒳 p𝒴 p𝒰 g f c G hf hc θ hθ)

end CategoryTheory.TwoFibreProductOver

end
