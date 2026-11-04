module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.StackIsom
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeStack
import all StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverDescent

/-!
# Descent data of a stack in groupoids, read through cocones

Effectivity of a descent datum, `CategoryTheory.Functor.DescentDatum.IsEffective`, is stated
through chosen restrictions. For a category fibred in groupoids it has an equivalent and much
more usable form: a *cocone*, that is an object `x` over the base together with morphisms
`ν i : D.x i ⟶ x` lying over the members of the covering family and compatible with the gluing
isomorphisms of the datum. In a category fibred in groupoids a morphism lying over a base
morphism exhibits its source as a restriction of its target, so the two formulations carry the
same information, and the cocone form is the one whose components can be read off along a
1-morphism of stacks.

This file develops that dictionary, together with two consequences used to descend objects of
the relative finite Hilbert category:

* a descent datum can be pushed forward along a 1-morphism over the base, so a cocone for the
  pushforward is obtained from the stack condition of the *target* of the 1-morphism;
* a *cartesian presentation* — a diagram of objects and morphisms over a covering family whose
  overlaps are genuine fibre products and whose transition morphisms are the identities — is
  itself a descent datum, so a stack in groupoids supplies a cocone for it.

The last section records the diagram of a descent datum relative to a *sieve*
(`CategoryTheory.Functor.SieveDescentDatum`) as a `CartesianSieveDiagram`: a family of objects
indexed by the arrows of the sieve, with cartesian transition squares that compose strictly.
Strict composability is what a cocone over a sieve needs, and it is the reason the diagram is
recorded separately rather than read off the sieve datum each time.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.mapRestriction`, the image of a chosen restriction
  under a 1-morphism over the base;
* `AlgebraicGeometry.Stack.FiniteHilbert.mapDescentDatum`, the image of a descent datum;
* `AlgebraicGeometry.Stack.FiniteHilbert.CartesianSieveDiagram`, a diagram over a sieve with
  cartesian, strictly composable transition squares;
* `AlgebraicGeometry.Stack.FiniteHilbert.sieveDatumMap`, the transition morphisms of a sieve
  descent datum.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.descentDatum_exists_cocone_of_isEffective` and
  `AlgebraicGeometry.Stack.FiniteHilbert.descentDatum_isEffective_of_cocone`: effectivity of a
  descent datum of a category fibred in groupoids is the existence of a cocone;
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_cocone_of_isStackInGroupoids`: a cocone for the
  pushforward of a descent datum along a 1-morphism into a stack in groupoids;
* `AlgebraicGeometry.Stack.FiniteHilbert.exists_cocone_of_cartesian_presentation`: a cocone for a
  cartesian presentation over a covering family.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.FiniteHilbert

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Pushing a descent datum forward along a 1-morphism over the base -/

section MapDescent

variable {C : Type u₁} [Category.{v₁} C]
  {A : BasedCategory.{v₂, u₂} C} {E : BasedCategory.{v₃, u₃} C}
  (G : A ⥤ᵇ E) (hE : E.p.IsFiberedInGroupoids)

/-- **The image of a chosen restriction under a 1-morphism over the base.** The image of the
structure morphism still lies over the same base morphism, and it is strongly cartesian because
the target is fibred in groupoids. -/
noncomputable def mapRestriction {U V : C} {f : V ⟶ U}
    {x : A.obj} {hx : A.p.obj x = U} (r : Restriction A.p f x hx) :
    Restriction E.p f (G.obj x) ((G.w_obj x).trans hx) := by
  have := r.isHomLift_hom
  have : E.p.IsHomLift f (G.map r.hom) := inferInstance
  have hpt := (G.w_obj r.pt).trans r.hpt
  have hx' := (G.w_obj x).trans hx
  exact { pt := G.obj r.pt
          hpt := hpt
          hom := G.map r.hom
          isHomLift := Functor.isHomLift_eqToHom hpt hx' inferInstance
          isCart := hE.isStronglyCartesian_homLift _ _ }

/-- The canonical comparison of two restrictions is carried to the canonical comparison of their
images. -/
lemma mapRestriction_compTo {U V W : C} (g : W ⟶ V) (f : V ⟶ U)
    {m : W ⟶ U} (hm : m = g ≫ f) {x : A.obj} {hx : A.p.obj x = U}
    (r : Restriction A.p f x hx) (rW : Restriction A.p m x hx) :
    G.map (Restriction.compTo A.p g f hm r rW) =
      Restriction.compTo E.p g f hm (mapRestriction G hE r) (mapRestriction G hE rW) := by
  refine Restriction.eq_compTo (p := E.p) g f hm
    (mapRestriction G hE r) (mapRestriction G hE rW) (G.map _) ?_ ?_
  · have hl : A.p.IsHomLift (eqToHom rW.hpt ≫ g ≫ eqToHom r.hpt.symm)
        (Restriction.compTo A.p g f hm r rW) := by
      unfold Restriction.compTo
      infer_instance
    have hl' : A.p.IsHomLift g (Restriction.compTo A.p g f hm r rW) := by
      refine IsHomLift.of_fac' A.p g _ rW.hpt r.hpt ?_
      simpa using IsHomLift.fac' A.p (eqToHom rW.hpt ≫ g ≫ eqToHom r.hpt.symm)
        (Restriction.compTo A.p g f hm r rW)
    -- `BasedFunctor.preserves_isHomLift` is named rather than reached by instance search: `hl`
    -- lifts the same morphism along a factorization through two `eqToHom`s, and the search can
    -- also go through it, which asks the unifier to identify that factorization with `g`.
    exact BasedFunctor.preserves_isHomLift G g (Restriction.compTo A.p g f hm r rW)
  · change G.map _ ≫ G.map r.hom = G.map rW.hom
    rw [← G.map_comp, Restriction.compTo_hom]

/-- A 1-morphism over the base carries a morphism of a fibre category to a morphism of a fibre
category. -/
lemma mapFibreHom {U : C} {a b : A.obj} {ha : A.p.obj a = U} {hb : A.p.obj b = U} {φ : a ⟶ b}
    (hφ : FibreHom A.p a b ha hb φ) :
    FibreHom E.p (G.obj a) (G.obj b) ((G.w_obj a).trans ha) ((G.w_obj b).trans hb) (G.map φ) := by
  have : A.p.IsHomLift (𝟙 U) φ := (Functor.fibreHomMk hφ).property
  exact Functor.fibreHom_of_isHomLift_id _ _ (by infer_instance)

/-- A 1-morphism over the base preserves the relation of being the canonical restriction of a
fibre morphism. -/
lemma mapIsRestrictionOf {W V Ux Uy : C} (g : W ⟶ V)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {mx : W ⟶ Ux} {my : W ⟶ Uy}
    (hfx : mx = g ≫ fx) (hfy : my = g ≫ fy)
    {x y : A.obj} {hx : A.p.obj x = Ux} {hy : A.p.obj y = Uy}
    (xr : Restriction A.p fx x hx) (yr : Restriction A.p fy y hy)
    (xrW : Restriction A.p mx x hx) (yrW : Restriction A.p my y hy)
    {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt}
    (h : IsRestrictionOf A.p g hfx hfy xr yr xrW yrW α β) :
    IsRestrictionOf E.p g hfx hfy (mapRestriction G hE xr) (mapRestriction G hE yr)
      (mapRestriction G hE xrW) (mapRestriction G hE yrW) (G.map α) (G.map β) := by
  change G.map β ≫ _ = _ ≫ G.map α
  rw [← mapRestriction_compTo, ← mapRestriction_compTo, ← G.map_comp, ← G.map_comp]
  exact congrArg G.map h

variable {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- **The image of a descent datum under a 1-morphism over the base.** Every component is the
image of the corresponding component; the cocycle condition is the image of the cocycle
condition. -/
noncomputable def mapDescentDatum
    (D : DescentDatum A.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    DescentDatum E.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x i := G.obj (D.x i)
  hx i := (G.w_obj (D.x i)).trans (D.hx i)
  xrij i j := mapRestriction G hE (D.xrij i j)
  xrji i j := mapRestriction G hE (D.xrji i j)
  φ i j := G.map (D.φ i j)
  φ_fibreHom i j := mapFibreHom G (D.φ_fibreHom i j)
  φ_iso i j := by
    have := D.φ_iso i j
    exact G.toFunctor.map_isIso _
  wi i j k := mapRestriction G hE (D.wi i j k)
  wj i j k := mapRestriction G hE (D.wj i j k)
  wk i j k := mapRestriction G hE (D.wk i j k)
  αij i j k := G.map (D.αij i j k)
  αjk i j k := G.map (D.αjk i j k)
  αik i j k := G.map (D.αik i j k)
  αij_restr i j k := mapIsRestrictionOf G hE _ _ _ _ _ _ _ (D.αij_restr i j k)
  αjk_restr i j k := mapIsRestrictionOf G hE _ _ _ _ _ _ _ (D.αjk_restr i j k)
  s₁₃ := D.s₁₃
  hs₁₃₁ := D.hs₁₃₁
  hs₁₃₂ := D.hs₁₃₂
  αik_restr i j k := mapIsRestrictionOf G hE _ _ _ _ _ _ _ (D.αik_restr i j k)
  -- Stated as a term rather than by `rw`: the two sides differ in the overlap objects, which are
  -- `mapRestriction` applied to those of `D`, and term elaboration identifies them while the
  -- unifier of `rw` does not.
  cocycle i j k := (congrArg G.map (D.cocycle i j k)).trans (G.map_comp _ _)

end MapDescent

/-! ### Effectivity read as a cocone -/

/-- A square of fibre morphisms is a restriction relation once the two canonical comparisons are
given by morphisms lying over `g` and compatible with the structure morphisms. -/
private theorem isRestrictionOf_of_hom_eq {C : Type u₁} [Category.{v₁} C] {X : Type u₂}
    [Category.{v₂} X] {p : X ⥤ C} {W V Ux Uy : C} (g : W ⟶ V)
    {fx : V ⟶ Ux} {fy : V ⟶ Uy} {mx : W ⟶ Ux} {my : W ⟶ Uy}
    (hfx : mx = g ≫ fx) (hfy : my = g ≫ fy) {x y : X} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : Restriction p fx x hx) (yr : Restriction p fy y hy)
    (xrW : Restriction p mx x hx) (yrW : Restriction p my y hy)
    {α : xr.pt ⟶ yr.pt} {β : xrW.pt ⟶ yrW.pt} (ψx : xrW.pt ⟶ xr.pt) (ψy : yrW.pt ⟶ yr.pt)
    (hψx : p.IsHomLift g ψx) (hψy : p.IsHomLift g ψy)
    (hx' : ψx ≫ xr.hom = xrW.hom) (hy' : ψy ≫ yr.hom = yrW.hom) (h : β ≫ ψy = ψx ≫ α) :
    IsRestrictionOf p g hfx hfy xr yr xrW yrW α β := by
  unfold IsRestrictionOf
  rwa [← Restriction.eq_compTo g fx hfx xr xrW ψx hψx hx',
    ← Restriction.eq_compTo g fy hfy yr yrW ψy hψy hy']

section Cocones

variable {C : Type u₁} [Category.{v₁} C] {A : BasedCategory.{v₂, u₂} C}
  {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- **An effective descent datum carries a cocone**: the inverse of the gluing isomorphism of
effectivity, composed with the structure morphism of the chosen restriction, is a morphism from
each component to the descended object, and the two copies on each overlap agree across the
gluing isomorphism of the datum. -/
lemma descentDatum_exists_cocone_of_isEffective
    (D : DescentDatum A.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (hD : D.IsEffective) :
    ∃ (x : A.obj) (_hx : A.p.obj x = U) (ν : ∀ i, D.x i ⟶ x),
      (∀ i, A.p.IsHomLift (f i) (ν i)) ∧
      ∀ i j, (D.xrij i j).hom ≫ ν i = D.φ i j ≫ (D.xrji i j).hom ≫ ν j := by
  classical
  obtain ⟨x, hx, xr, ψ, hψlift, hψiso, hcompat⟩ := hD
  have hiso (i : I) : IsIso (ψ i) := hψiso i
  let ν (i : I) : D.x i ⟶ x := inv (ψ i) ≫ (xr i).hom
  refine ⟨x, hx, ν, ?_, ?_⟩
  · intro i
    have h1 : A.p.IsHomLift (𝟙 (V i)) (ψ i) := (Functor.fibreHomMk (hψlift i)).property
    have h2 : A.p.IsHomLift (𝟙 (V i)) (inv (ψ i)) := by
      simpa using IsHomLift.inv A.p (𝟙 (V i)) (ψ i)
    have h3 := (xr i).isHomLift_hom
    exact Functor.isHomLift_of_eq (n := 𝟙 (V i) ≫ f i) (φ := ν i)
      (by dsimp only [ν]; infer_instance) (by simp)
  · intro i j
    obtain ⟨r, ψir, ψjr, hir, hjr, hiiso, hjiso, hi, hj, hij⟩ := hcompat i j
    have := hiiso
    have ci : Restriction.compTo A.p (pr₁ i j) (𝟙 (V i)) (by simp)
        (Restriction.id A.p (D.x i) (D.hx i)) (D.xrij i j) = (D.xrij i j).hom :=
      (Restriction.eq_compTo _ _ _ _ _ _ (D.xrij i j).isHomLift_hom (Category.comp_id _)).symm
    have cj : Restriction.compTo A.p (pr₂ i j) (𝟙 (V j)) (by simp)
        (Restriction.id A.p (D.x j) (D.hx j)) (D.xrji i j) = (D.xrji i j).hom :=
      (Restriction.eq_compTo _ _ _ _ _ _ (D.xrji i j).isHomLift_hom (Category.comp_id _)).symm
    change ψir ≫ _ = _ ≫ ψ i at hi
    change ψjr ≫ _ = _ ≫ ψ j at hj
    rw [ci] at hi
    rw [cj] at hj
    have hi' : ψir ≫ (D.xrij i j).hom ≫ ν i = r.hom := by
      dsimp only [ν]
      rw [← Category.assoc ψir, hi]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, Restriction.compTo_hom]
    have hj' : ψjr ≫ (D.xrji i j).hom ≫ ν j = r.hom := by
      dsimp only [ν]
      rw [← Category.assoc ψjr, hj]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, Restriction.compTo_hom]
    refine (cancel_epi ψir).mp ?_
    simpa only [Category.assoc, ← hij] using hi'.trans hj'.symm

/-- **A cocone makes a descent datum of a category fibred in groupoids effective.** Each morphism
of the cocone exhibits the corresponding component as a restriction of the descended object, so
the gluing isomorphisms of effectivity may be taken to be the identities. -/
lemma descentDatum_isEffective_of_cocone (hA : A.p.IsFiberedInGroupoids)
    (D : DescentDatum A.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (x : A.obj) (hx : A.p.obj x = U) (ν : ∀ i, D.x i ⟶ x)
    (hν : ∀ i, A.p.IsHomLift (f i) (ν i))
    (hcompat : ∀ i j, D.φ i j ≫ (D.xrji i j).hom ≫ ν j = (D.xrij i j).hom ≫ ν i) :
    D.IsEffective := by
  have hcart (i : I) : A.p.IsStronglyCartesian (f i) (ν i) := by
    have := hν i
    exact hA.isStronglyCartesian_homLift _ _
  refine ⟨x, hx, fun i => Restriction.ofCartesian (D.hx i) hx _ (hcart i),
    fun i => 𝟙 (D.x i), fun i => Functor.fibreHom_of_isHomLift_id _ _ (IsHomLift.id (D.hx i)),
    fun i => IsIso.id (D.x i), fun i j => ?_⟩
  have hcartij : A.p.IsStronglyCartesian (pr₁ i j ≫ f i) ((D.xrij i j).hom ≫ ν i) := by
    have := (D.xrij i j).isStronglyCartesian_hom
    have := hcart i
    infer_instance
  refine ⟨Restriction.ofCartesian (D.xrij i j).hpt hx _ hcartij,
    𝟙 (D.xrij i j).pt, D.φ i j,
    Functor.fibreHom_of_isHomLift_id _ _ (IsHomLift.id (D.xrij i j).hpt), D.φ_fibreHom i j,
    IsIso.id (D.xrij i j).pt, D.φ_iso i j, ?_, ?_, Category.id_comp _⟩
  · exact isRestrictionOf_of_hom_eq _ _ _ _ _ _ _ (D.xrij i j).hom (D.xrij i j).hom
      (D.xrij i j).isHomLift_hom (D.xrij i j).isHomLift_hom rfl (Category.comp_id _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  · have hφlift : A.p.IsHomLift (pr₂ i j) (D.φ i j ≫ (D.xrji i j).hom) := by
      have h1 : A.p.IsHomLift (𝟙 (Vij i j)) (D.φ i j) :=
        (Functor.fibreHomMk (D.φ_fibreHom i j)).property
      have h2 := (D.xrji i j).isHomLift_hom
      exact Functor.isHomLift_of_eq (n := 𝟙 (Vij i j) ≫ pr₂ i j) inferInstance (by simp)
    exact isRestrictionOf_of_hom_eq _ _ _ _ _ _ _ (D.φ i j ≫ (D.xrji i j).hom) (D.xrji i j).hom
      hφlift (D.xrji i j).isHomLift_hom ((Category.assoc _ _ _).trans (hcompat i j))
      (Category.comp_id _) (Category.comp_id _).symm

end Cocones

/-! ### Cocones supplied by a stack in groupoids -/

section StackCocones

variable {C : Type u₁} [Category.{v₁} C]
  {A : BasedCategory.{v₂, u₂} C} {E : BasedCategory.{v₃, u₃} C} (G : A ⥤ᵇ E)
  {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → C}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

/-- **The component of a descent datum along a 1-morphism into a stack in groupoids has a
cocone.** The datum is pushed forward along the 1-morphism, where the descent condition of the
stack makes it effective. -/
lemma exists_cocone_of_isStackInGroupoids {J : GrothendieckTopology C}
    (hs : E.p.IsStackInGroupoids.{w} J) (hf : Sieve.ofArrows V f ∈ J U)
    (D : DescentDatum A.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    ∃ (x : E.obj) (_hx : E.p.obj x = U) (ν : ∀ i, G.obj (D.x i) ⟶ x),
      (∀ i, E.p.IsHomLift (f i) (ν i)) ∧
      ∀ i j, G.map (D.xrij i j).hom ≫ ν i =
        G.map (D.φ i j) ≫ G.map (D.xrji i j).hom ≫ ν j :=
  descentDatum_exists_cocone_of_isEffective
    (mapDescentDatum G hs.isFiberedInGroupoids D)
    (hs.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ _)

include hVij hVijk hq₁ hq₂ hq₃ in
/-- **A cartesian presentation over a covering family of a stack in groupoids has a cocone.**
A *cartesian presentation* is a diagram of objects over a covering family and over its double
and triple overlaps, with morphisms lying over the projections which commute on the nose. It is
a descent datum whose gluing isomorphisms are the identities, so the descent condition of the
stack supplies a cocone for it. -/
lemma exists_cocone_of_cartesian_presentation {J : GrothendieckTopology C}
    (hs : E.p.IsStackInGroupoids.{w} J) (hf : Sieve.ofArrows V f ∈ J U)
    (t : I → E.obj) (ht : ∀ i, E.p.obj (t i) = V i)
    (tij : I → I → E.obj) (htij : ∀ i j, E.p.obj (tij i j) = Vij i j)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hc : ∀ i j, E.p.IsHomLift (pr₁ i j) (c i j))
    (he : ∀ i j, E.p.IsHomLift (pr₂ i j) (e i j))
    (tijk : I → I → I → E.obj) (htijk : ∀ i j k, E.p.obj (tijk i j k) = Vijk i j k)
    (a₁ : ∀ i j k, tijk i j k ⟶ t i) (a₂ : ∀ i j k, tijk i j k ⟶ t j)
    (a₃ : ∀ i j k, tijk i j k ⟶ t k)
    (ha₁ : ∀ i j k, E.p.IsHomLift (q₁ i j k) (a₁ i j k))
    (ha₂ : ∀ i j k, E.p.IsHomLift (q₂ i j k) (a₂ i j k))
    (ha₃ : ∀ i j k, E.p.IsHomLift (q₃ i j k) (a₃ i j k))
    (s₁₃ : ∀ i j k, Vijk i j k ⟶ Vij i k)
    (hs₁₃₁ : ∀ i j k, s₁₃ i j k ≫ pr₁ i k = q₁ i j k)
    (hs₁₃₂ : ∀ i j k, s₁₃ i j k ≫ pr₂ i k = q₃ i j k)
    (b₁₂ : ∀ i j k, tijk i j k ⟶ tij i j) (b₂₃ : ∀ i j k, tijk i j k ⟶ tij j k)
    (b₁₃ : ∀ i j k, tijk i j k ⟶ tij i k)
    (hb₁₂ : ∀ i j k, E.p.IsHomLift (s₁₂ i j k) (b₁₂ i j k))
    (hb₂₃ : ∀ i j k, E.p.IsHomLift (s₂₃ i j k) (b₂₃ i j k))
    (hb₁₃ : ∀ i j k, E.p.IsHomLift (s₁₃ i j k) (b₁₃ i j k))
    (h₁₂₁ : ∀ i j k, b₁₂ i j k ≫ c i j = a₁ i j k)
    (h₁₂₂ : ∀ i j k, b₁₂ i j k ≫ e i j = a₂ i j k)
    (h₂₃₂ : ∀ i j k, b₂₃ i j k ≫ c j k = a₂ i j k)
    (h₂₃₃ : ∀ i j k, b₂₃ i j k ≫ e j k = a₃ i j k)
    (h₁₃₁ : ∀ i j k, b₁₃ i j k ≫ c i k = a₁ i j k)
    (h₁₃₃ : ∀ i j k, b₁₃ i j k ≫ e i k = a₃ i j k) :
    ∃ (x : E.obj) (_hx : E.p.obj x = U) (ν : ∀ i, t i ⟶ x),
      (∀ i, E.p.IsHomLift (f i) (ν i)) ∧ ∀ i j, c i j ≫ ν i = e i j ≫ ν j := by
  have hcart {X Y : C} {a b : E.obj} {g : X ⟶ Y} {φ : a ⟶ b} (hφ : E.p.IsHomLift g φ) :
      E.p.IsStronglyCartesian g φ :=
    hs.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have hrestr {T W X Y : C} {m : T ⟶ X} {n : T ⟶ Y} {g : W ⟶ X} {g' : W ⟶ Y}
      {a b z t' : E.obj} {ha : E.p.obj a = X} {hb : E.p.obj b = Y}
      {hz : E.p.obj z = W} {ht' : E.p.obj t' = T}
      {c' : z ⟶ a} {e' : z ⟶ b} {x : t' ⟶ a} {y : t' ⟶ b}
      (hc' : E.p.IsHomLift g c') (he' : E.p.IsHomLift g' e')
      (hx : E.p.IsHomLift m x) (hy : E.p.IsHomLift n y)
      (k : T ⟶ W) (hm : m = k ≫ g) (hn : n = k ≫ g')
      (β : t' ⟶ z) (hβ : E.p.IsHomLift k β) (hβc : β ≫ c' = x) (hβe : β ≫ e' = y) :
      IsRestrictionOf E.p k hm hn
        (Restriction.ofCartesian hz ha c' (hcart hc'))
        (Restriction.ofCartesian hz hb e' (hcart he'))
        (Restriction.ofCartesian ht' ha x (hcart hx))
        (Restriction.ofCartesian ht' hb y (hcart hy)) (𝟙 z) (𝟙 t') := by
    exact isRestrictionOf_of_hom_eq k hm hn _ _ _ _ β β hβ hβ hβc hβe
      ((Category.id_comp β).trans (Category.comp_id β).symm)
  let D : Functor.DescentDatum E.p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ :=
    { x := t
      hx := ht
      xrij i j := Restriction.ofCartesian (htij i j) (ht i) _ (hcart (hc i j))
      xrji i j := Restriction.ofCartesian (htij i j) (ht j) _ (hcart (he i j))
      φ i j := 𝟙 (tij i j)
      φ_fibreHom i j := Functor.fibreHom_of_isHomLift_id _ _ (IsHomLift.id (htij i j))
      φ_iso i j := IsIso.id _
      wi i j k := Restriction.ofCartesian (htijk i j k) (ht i) _ (hcart (ha₁ i j k))
      wj i j k := Restriction.ofCartesian (htijk i j k) (ht j) _ (hcart (ha₂ i j k))
      wk i j k := Restriction.ofCartesian (htijk i j k) (ht k) _ (hcart (ha₃ i j k))
      αij i j k := 𝟙 (tijk i j k)
      αjk i j k := 𝟙 (tijk i j k)
      αik i j k := 𝟙 (tijk i j k)
      αij_restr i j k := hrestr (hc i j) (he i j) (ha₁ i j k) (ha₂ i j k)
        _ _ _ _ (hb₁₂ i j k) (h₁₂₁ i j k) (h₁₂₂ i j k)
      αjk_restr i j k := hrestr (hc j k) (he j k) (ha₂ i j k) (ha₃ i j k)
        _ _ _ _ (hb₂₃ i j k) (h₂₃₂ i j k) (h₂₃₃ i j k)
      s₁₃ := s₁₃
      hs₁₃₁ := hs₁₃₁
      hs₁₃₂ := hs₁₃₂
      αik_restr i j k := hrestr (hc i k) (he i k) (ha₁ i j k) (ha₃ i j k)
        _ _ _ _ (hb₁₃ i j k) (h₁₃₁ i j k) (h₁₃₃ i j k)
      cocycle i j k := (Category.id_comp _).symm }
  obtain ⟨x, hx, ν, hν, hcompat⟩ := descentDatum_exists_cocone_of_isEffective D
    (hs.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D)
  refine ⟨x, hx, ν, hν, fun i j => ?_⟩
  have h := hcompat i j
  change c i j ≫ ν i = 𝟙 (tij i j) ≫ e i j ≫ ν j at h
  simpa only [Category.id_comp] using h

end StackCocones

/-! ### Diagrams over a sieve with cartesian transition squares -/

section SieveDiagram

variable {C : Type u₁} [Category.{v₁} C] {U : C}

/-- **A diagram over a sieve with cartesian, strictly composable transition squares.** To each
arrow `f` of the sieve it attaches an object `obj f` with a structure morphism `q f` to the
source of `f`, and to each factorization `g = a ≫ f` a transition morphism presenting `obj g` as
the base change of `obj f` along `a`. The transition morphisms are required to compose
*strictly*, which is what lets a cocone over the diagram be assembled arrow by arrow. -/
structure CartesianSieveDiagram (R : Sieve U) where
  /-- The object attached to an arrow of the sieve. -/
  obj {V : C} (f : V ⟶ U) (hf : R f) : C
  /-- Its structure morphism to the source of the arrow. -/
  q {V : C} (f : V ⟶ U) (hf : R f) : obj f hf ⟶ V
  /-- The transition morphism attached to a factorization of one arrow through another. -/
  map {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : obj g hg ⟶ obj f hf
  /-- A transition morphism presents its source as a base change of its target. -/
  square {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : IsPullback (map hf hg a ha) (q g hg) (q f hf) a
  /-- The transition morphisms compose strictly. -/
  map_comp {V W Z : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : W ⟶ V) (a' : Z ⟶ W)
    (ha : a ≫ f = g) (ha' : a' ≫ g = b) :
    map hg hb a' ha' ≫ map hf hg a ha =
      map hf hb (a' ≫ a) (by rw [Category.assoc, ha, ha'])

namespace CartesianSieveDiagram

variable {R : Sieve U} (D : CartesianSieveDiagram R)

/-- **Transporting a morphism into one component of the diagram to another component.** A
morphism `x : T ⟶ obj f` together with a morphism `a : T ⟶ W` over the base factors through the
component at `x ≫ q f ≫ f` and then transitions into the component at `g`. -/
noncomputable def transport {V W T : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (x : T ⟶ D.obj f hf) (a : T ⟶ W) (h : x ≫ D.q f hf ≫ f = a ≫ g) : T ⟶ D.obj g hg :=
  let hb := R.downward_closed hf (x ≫ D.q f hf)
  (D.square hf hb (x ≫ D.q f hf) rfl).lift x (𝟙 T) (by simp) ≫
    D.map hg hb a (by simpa only [Category.assoc] using h.symm)

/-- Transporting a morphism keeps the morphism over the base it was transported along. -/
lemma transport_q {V W T : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (x : T ⟶ D.obj f hf) (a : T ⟶ W) (h : x ≫ D.q f hf ≫ f = a ≫ g) :
    D.transport hf hg x a h ≫ D.q g hg = a := by
  dsimp [transport]
  rw [Category.assoc, (D.square _ _ _ _).w, ← Category.assoc,
    (D.square _ _ _ _).lift_snd, Category.id_comp]

/-- Transporting a morphism that already factors through a third component of the diagram is
the transition morphism of that factorization. -/
lemma transport_of_map {V W T Y : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Y ⟶ U} (hb : R b) (a : Y ⟶ V) (a' : Y ⟶ W)
    (ha : a ≫ f = b) (ha' : a' ≫ g = b) (x : T ⟶ D.obj b hb)
    (h : (x ≫ D.map hf hb a ha) ≫ D.q f hf ≫ f = (x ≫ D.q b hb ≫ a') ≫ g) :
    D.transport hf hg (x ≫ D.map hf hb a ha) (x ≫ D.q b hb ≫ a') h =
      x ≫ D.map hg hb a' ha' := by
  let c := (x ≫ D.map hf hb a ha) ≫ D.q f hf
  have hc : c = (x ≫ D.q b hb) ≫ a := by
    simp only [c, Category.assoc, (D.square hf hb a ha).w]
  have hc' : (x ≫ D.q b hb) ≫ b = c ≫ f := by simp only [hc, Category.assoc, ha]
  let hcR := R.downward_closed hf c
  let l := (D.square hf hcR c rfl).lift (x ≫ D.map hf hb a ha) (𝟙 T) (by simp [c])
  have hl : l ≫ D.map hb hcR (x ≫ D.q b hb) hc' = x := by
    refine (D.square hf hb a ha).hom_ext ?_ ?_
    · rw [Category.assoc, D.map_comp]
      simpa only [← hc] using (D.square hf hcR c rfl).lift_fst
        (x ≫ D.map hf hb a ha) (𝟙 T) (by simp [c])
    · rw [Category.assoc, (D.square hb hcR _ hc').w, ← Category.assoc,
        (D.square hf hcR c rfl).lift_snd, Category.id_comp]
  change l ≫ D.map hg hcR _ _ = _
  calc _ = l ≫ (D.map hb hcR (x ≫ D.q b hb) hc' ≫ D.map hg hb a' ha') := by
        rw [D.map_comp]
        simp only [Category.assoc]
    _ = _ := by rw [← Category.assoc, hl]

/-- Transporting a morphism into the component it already lands in changes nothing. -/
lemma transport_self {V T : C} {f : V ⟶ U} (hf : R f) (x : T ⟶ D.obj f hf) :
    D.transport hf hf x (x ≫ D.q f hf) (by simp only [Category.assoc]) = x := by
  dsimp [transport]
  exact (D.square _ _ _ _).lift_fst _ _ _

/-- Transport is transitive: transporting twice is transporting once. -/
lemma transport_comp {V W Z T : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (x : T ⟶ D.obj f hf) (a : T ⟶ W) (a' : T ⟶ Z)
    (ha : x ≫ D.q f hf ≫ f = a ≫ g) (ha' : a ≫ g = a' ≫ b) :
    D.transport hg hb (D.transport hf hg x a ha) a'
        (by rw [← Category.assoc, D.transport_q]; exact ha') =
      D.transport hf hb x a' (ha.trans ha') := by
  let hc := R.downward_closed hf (x ≫ D.q f hf)
  let l := (D.square hf hc (x ≫ D.q f hf) rfl).lift x (𝟙 T) (by simp)
  have hl : l ≫ D.q _ hc = 𝟙 T := (D.square _ _ _ _).lift_snd _ _ _
  have hh : (l ≫ D.map hg hc a (by simpa only [Category.assoc] using ha.symm)) ≫
      D.q g hg ≫ g = (l ≫ D.q _ hc ≫ a') ≫ b := by
    simp only [Category.assoc, reassoc_of% (D.square hg hc a _).w]
    simpa only [← Category.assoc l (D.q _ hc), hl, Category.id_comp] using ha'
  change D.transport hg hb (l ≫ D.map hg hc a _) a' _ = l ≫ D.map hb hc a' _
  simpa only [← Category.assoc l, hl, Category.id_comp] using
    D.transport_of_map hg hb hc a a' _
      (by simpa only [Category.assoc] using (ha.trans ha').symm) l hh

/-- Transport commutes with precomposition in the source of the morphism transported. -/
lemma transport_precomp {V W T T' : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (x : T ⟶ D.obj f hf) (a : T ⟶ W) (h : x ≫ D.q f hf ≫ f = a ≫ g) (t : T' ⟶ T) :
    D.transport hf hg (t ≫ x) (t ≫ a)
        (by simpa only [Category.assoc] using congrArg (fun k => t ≫ k) h) =
      t ≫ D.transport hf hg x a h := by
  let hb := R.downward_closed hf (x ≫ D.q f hf)
  let l := (D.square hf hb (x ≫ D.q f hf) rfl).lift x (𝟙 T) (by simp)
  have hl : l ≫ D.map hf hb (x ≫ D.q f hf) rfl = x := (D.square _ _ _ _).lift_fst _ _ _
  have hq : l ≫ D.q _ hb = 𝟙 T := (D.square _ _ _ _).lift_snd _ _ _
  have hh : ((t ≫ l) ≫ D.map hf hb (x ≫ D.q f hf) rfl) ≫ D.q f hf ≫ f =
      ((t ≫ l) ≫ D.q _ hb ≫ a) ≫ g := by
    simp only [Category.assoc, hl, ← Category.assoc l, hq, Category.id_comp]
    simpa only [Category.assoc] using congrArg (fun k => t ≫ k) h
  change D.transport hf hg (t ≫ x) (t ≫ a) _ = t ≫ (l ≫ D.map hg hb a _)
  simpa only [Category.assoc, hl, ← Category.assoc l, hq, Category.id_comp] using
    D.transport_of_map hf hg hb (x ≫ D.q f hf) a rfl
      (by simpa only [Category.assoc] using h.symm) (t ≫ l) hh

/-- The transition morphism of a trivial factorization is the identity. -/
lemma map_id {V : C} {f : V ⟶ U} (hf : R f) : D.map hf hf (𝟙 V) (by simp) = 𝟙 _ := by
  refine (D.square hf hf (𝟙 V) (by simp)).hom_ext ?_ ?_
  · simpa using D.map_comp hf hf hf (𝟙 V) (𝟙 V) (by simp) (by simp)
  · simpa using (D.square hf hf (𝟙 V) (by simp)).w

/-- Transporting back along a transition morphism just applied changes nothing. -/
lemma transport_map {V W T : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) (x : T ⟶ D.obj g hg) :
    D.transport hf hg (x ≫ D.map hf hg a ha) (x ≫ D.q g hg)
      (by simp only [Category.assoc, reassoc_of% (D.square hf hg a ha).w, ha]) = x := by
  simpa only [Category.comp_id, D.map_id] using
    D.transport_of_map hf hg hg a (𝟙 W) ha (by simp) x
      (by simp only [Category.assoc, reassoc_of% (D.square hf hg a ha).w, ha, Category.comp_id])

/-- Transporting out of a component reached by a transition morphism is transporting out of the
component that transition morphism came from. -/
lemma transport_map_comp {V W Z T : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : W ⟶ V) (ha : a ≫ f = g)
    (x : T ⟶ D.obj g hg) (a' : T ⟶ Z) (h : x ≫ D.q g hg ≫ g = a' ≫ b) :
    D.transport hf hb (x ≫ D.map hf hg a ha) a'
        (by simp only [Category.assoc, reassoc_of% (D.square hf hg a ha).w, ha]; exact h) =
      D.transport hg hb x a' h := by
  have he := D.transport_comp hf hg hb (x ≫ D.map hf hg a ha) (x ≫ D.q g hg) a'
    (by simp only [Category.assoc, reassoc_of% (D.square hf hg a ha).w, ha])
    (by simpa only [Category.assoc] using h)
  simp only [D.transport_map] at he
  exact he.symm

end CartesianSieveDiagram

end SieveDiagram

end AlgebraicGeometry.Stack.FiniteHilbert

end

/-! ### The transition morphisms of a descent datum relative to a sieve

The transport of a sieve-indexed descent datum along a factorization of one arrow of its sieve
through another, `AlgebraicGeometry.Stack.FiniteHilbert.sieveDatumMap`, with three facts about
it: it lies cartesianly over the factorization, it absorbs a contraction of the datum into a
gluing isomorphism, and it composes along composite factorizations. -/

public section

namespace AlgebraicGeometry.Stack.FiniteHilbert

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {p : E ⥤ C} [p.IsFibered] {U : C} {R : Sieve U}

/-- **The transition morphism of a descent datum relative to a sieve.** For two arrows `f` and
`g` of the sieve and a factorization `g = a ≫ f`, the component of the datum at `g` maps to the
component at `f`: contract the datum along `a` and compose with the chosen pullback. -/
noncomputable def sieveDatumMap (D : SieveDescentDatum p R)
    {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : (D.obj g hg).1 ⟶ (D.obj f hf).1 :=
  datumMap D hf hg a ha

/-- The transition morphism of a descent datum lies cartesianly over its factorization. -/
theorem sieveDatumMap_cartesian (D : SieveDescentDatum p R)
    {V W : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (a : W ⟶ V) (ha : a ≫ f = g) : p.IsCartesian a (sieveDatumMap D hf hg a ha) :=
  datumMap_cartesian D hf hg a ha

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion in
/-- The transition morphism absorbs a contraction of the datum into a gluing isomorphism. -/
theorem sieveDatumMap_glue (D : SieveDescentDatum p R)
    {V W Z : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : Z ⟶ V) (a' : Z ⟶ W)
    (ha : a ≫ f = b) (ha' : a' ≫ g = b) :
    Fiber.fiberInclusion.map (D.contract hf a hb ha).hom ≫ sieveDatumMap D hg hb a' ha' =
      Fiber.fiberInclusion.map (D.iso hf hg a a' (ha.trans ha'.symm)).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 a' :=
  datumMap_glue D hf hg hb a a' ha ha'

/-- The transition morphisms of a descent datum compose along composite factorizations. -/
theorem sieveDatumMap_comp (D : SieveDescentDatum p R)
    {V W Z : C} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    {b : Z ⟶ U} (hb : R b) (a : W ⟶ V) (a' : Z ⟶ W)
    (ha : a ≫ f = g) (ha' : a' ≫ g = b) :
    sieveDatumMap D hg hb a' ha' ≫ sieveDatumMap D hf hg a ha =
      sieveDatumMap D hf hb (a' ≫ a) (by rw [Category.assoc, ha, ha']) :=
  datumMap_comp D hf hg hb a a' ha ha'

end AlgebraicGeometry.Stack.FiniteHilbert

end
