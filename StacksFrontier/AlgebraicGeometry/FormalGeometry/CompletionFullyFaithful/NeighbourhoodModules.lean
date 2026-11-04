module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods

/-!
# Sections of a module on an open neighbourhood of a closed subscheme

Let `i : Y ⟶ X` be a closed immersion of schemes and let `Y_n ⊂ X` be the infinitesimal
neighbourhoods of `Y` in `X`. An open `V ⊆ X` containing `Y` contains every `Y_n`, so each
structure morphism `Y_n ⟶ X` lifts uniquely through the open immersion `V ⟶ X`; the lifted tower
exhibits `Y_n` as the `n`-th infinitesimal neighbourhood of `Y` inside `V`. This file sets up that
tower and the comparison

`colim_W Γ(W, E) ⟶ lim_n Γ(Y_n, E|_{Y_n})`

for a module `E` on `V`, where `W` runs over the opens of `V` containing `Y`. It is the comparison
occurring in conditions (3) and (4) of [Stacks, Tag 0EK2], which differ from conditions (1) and (2)
of that tag exactly in that the module is allowed to live on a neighbourhood instead of on `X`.

## Main definitions

* `Stacks.Algebraization.InfinitesimalTower` — a tower of schemes over a scheme `Z` whose terms all
  have their image inside a fixed subset of `Z`. The comparison and its stability properties are
  developed for such a tower.
* `Stacks.Algebraization.InfinitesimalTower.sectionsAt` — restriction of a section over an open
  containing the support to the `n`-th term of the tower.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete` — the comparison above, spelled out
  by the universal properties of the filtered colimit and the inverse limit.
* `Stacks.Algebraization.liftToOpen` — the factorization of a morphism through an open containing
  its image.
* `Stacks.Algebraization.nbhdImmersion` and `Stacks.Algebraization.nbhdTower` — the closed
  immersion `Y ⟶ V` induced by `i`, and the tower of infinitesimal neighbourhoods of `Y` read over
  `V`.
* `Stacks.Algebraization.IsNeighbourhoodSectionsCompleteOn` — the comparison at the latter tower.

## Main results

* `Stacks.Algebraization.InfinitesimalTower.sectionsAt_restrict` — the comparison does not see a
  shrinking of the open.
* `Stacks.Algebraization.InfinitesimalTower.sectionsAt_natural` — the comparison is natural in the
  module.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_iso` — the comparison only
  depends on the isomorphism class of the module.
* `Stacks.Algebraization.existsUnique_lift` — a morphism whose image lies in an open factors
  through that open, uniquely.

## Implementation notes

Everything is proved for an abstract `InfinitesimalTower` and only then instantiated. The concrete
tower over `V` is built from `AlgebraicGeometry.IsOpenImmersion.lift`, which is a very large term,
and the proofs below force several definitional comparisons of modules pulled back along the
tower's structure morphisms; carrying those out with the lift in place exhausts the kernel's
budget, whereas against an abstract tower there is nothing to unfold and instantiating a finished
statement is a substitution. For the same reason `liftToOpen` is extracted from the uniqueness
statement `existsUnique_lift` rather than being `IsOpenImmersion.lift` itself: the factorization is
unique, so nothing is lost, and the tower's structure morphism is then opaque.

The tower over `V` has the *terms* of the tower over `X`, with their structure morphisms factored
through `V`, rather than the tower rebuilt from the induced immersion `Y ⟶ V`. The two agree as
subschemes of `V`, but sharing the terms is what lets conditions (1) and (2) of the tag, which are
about modules on `X`, be compared with condition (3), which is about modules on `V`.

As in the Stacks 0EKP and 0EK2 files this subtree draws on, `rw` cannot cross the projection
separating `Γ(E, W)` from a presheaf's sections, so the transport along an isomorphism is in term
mode, using `NatTrans.naturality_apply` in place of a rewrite.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

/-! ### The comparison for an abstract tower -/

/-- A tower of schemes over `Z`, all of whose terms have their image inside a fixed subset of `Z`.
The infinitesimal neighbourhoods of a closed subscheme, read over an open neighbourhood of it,
form such a tower. -/
public structure InfinitesimalTower (Z : Scheme.{u}) where
  /-- The `n`-th term of the tower, as a scheme over `Z`. -/
  obj : ℕ → Over Z
  /-- The inclusion of the `n`-th term into the `m`-th one for `n ≤ m`. -/
  trans : ∀ (n m : ℕ), n ≤ m → (obj n ⟶ obj m)
  /-- The subset of `Z` the tower is supported in. -/
  support : Set Z
  /-- Every term of the tower has its image inside the support. -/
  range_hom_subset : ∀ n : ℕ, Set.range (obj n).hom.base ⊆ support

namespace InfinitesimalTower

variable {Z : Scheme.{u}} (T : InfinitesimalTower Z)

/-- An open containing the support contains every term of the tower. -/
public theorem preimage_eq_top {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ) :
    (T.obj n).hom ⁻¹ᵁ W = ⊤ :=
  le_antisymm le_top fun x _ => hW (T.range_hom_subset n (Set.mem_range_self x))

/-- Restriction of a section over an open containing the support to the `n`-th term. -/
public def sectionsAt (E : Z.Modules) {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ) :
    Γ(E, W) ⟶ Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤) :=
  pullbackSectionsAt (T.obj n).hom E (T.preimage_eq_top hW n)

/-- Shrinking the open does not change the induced section on the `n`-th term. -/
public theorem sectionsAt_restrict (E : Z.Modules) {W W' : Z.Opens} (h : W' ≤ W)
    (hW : T.support ⊆ W) (hW' : T.support ⊆ W') (n : ℕ) (t : Γ(E, W)) :
    T.sectionsAt E hW' n (E.presheaf.map (homOfLE h).op t) = T.sectionsAt E hW n t :=
  pullbackSectionsAt_restrict _ E h _ _ t

/-- Naturality of the comparison in the module. -/
public theorem sectionsAt_natural {E F : Z.Modules} (φ : E ⟶ F) {W : Z.Opens}
    (hW : T.support ⊆ W) (n : ℕ) (t : Γ(E, W)) :
    T.sectionsAt F hW n (φ.app W t) =
      ((Scheme.Modules.pullback (T.obj n).hom).map φ).app ⊤ (T.sectionsAt E hW n t) :=
  pullbackSectionsAt_natural _ φ _ t

/-- Naturality of the transition maps of the inverse system in the module. -/
public theorem transSections_natural {E F : Z.Modules} (φ : E ⟶ F) {n m : ℕ} (hnm : n ≤ m)
    (sm : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)) :
    pullbackSectionsMap F (T.trans n m hnm)
        (((Scheme.Modules.pullback (T.obj m).hom).map φ).app ⊤ sm) =
      ((Scheme.Modules.pullback (T.obj n).hom).map φ).app ⊤
        (pullbackSectionsMap E (T.trans n m hnm) sm) :=
  pullbackSectionsMap_natural φ (T.trans n m hnm) sm

/-- A compatible family transported along a morphism of modules is compatible. -/
public theorem isCompatible_map {E F : Z.Modules} (φ : E ⟶ F)
    {s : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤)}
    (hs : ∀ (n m : ℕ) (h : n ≤ m), pullbackSectionsMap E (T.trans n m h) (s m) = s n) :
    ∀ (n m : ℕ) (h : n ≤ m),
      pullbackSectionsMap F (T.trans n m h)
          (((Scheme.Modules.pullback (T.obj m).hom).map φ).app ⊤ (s m)) =
        ((Scheme.Modules.pullback (T.obj n).hom).map φ).app ⊤ (s n) :=
  fun n m hnm =>
    (T.transSections_natural φ hnm (s m)).trans
      (congrArg (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map φ).app ⊤ v) (hs n m hnm))

/-- The colimit of the sections of `E` over the opens containing the support of the tower is the
inverse limit of the sections of `E` on the terms of the tower: every compatible family comes from
such an open, and two sections inducing the same family agree on a smaller one. -/
public structure IsSectionsComplete (E : Z.Modules) : Prop where
  /-- Every compatible family of sections on the terms of the tower comes from a section over
  some open containing the support. -/
  exists_section : ∀ s : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤),
      (∀ (n m : ℕ) (h : n ≤ m), pullbackSectionsMap E (T.trans n m h) (s m) = s n) →
      ∃ (W : Z.Opens) (hW : T.support ⊆ W) (t : Γ(E, W)),
        ∀ n : ℕ, T.sectionsAt E hW n t = s n
  /-- Two sections over opens containing the support which induce the same family on the terms of
  the tower agree on a smaller open. -/
  eq_of_sectionsAt_eq : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W')
      (t : Γ(E, W)) (u : Γ(E, W')),
      (∀ n : ℕ, T.sectionsAt E hW n t = T.sectionsAt E hW' n u) →
      ∃ (W'' : Z.Opens) (_ : T.support ⊆ W'') (h₁ : W'' ≤ W) (h₂ : W'' ≤ W'),
        E.presheaf.map (homOfLE h₁).op t = E.presheaf.map (homOfLE h₂).op u

/-- The pullback of an isomorphism of modules is inverted by the pullback of its inverse. -/
public theorem app_pullback_map_inv_hom {W : Scheme.{u}} (g : W ⟶ Z) {E F : Z.Modules}
    (e : E ≅ F) (x : Γ((Scheme.Modules.pullback g).obj F, ⊤)) :
    ((Scheme.Modules.pullback g).map e.hom).app ⊤
        (((Scheme.Modules.pullback g).map e.inv).app ⊤ x) = x :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ x)
    (((Scheme.Modules.pullback g).mapIso e).inv_hom_id)

/-- An isomorphism of modules is inverted by its inverse on sections. -/
public theorem app_inv_hom {E F : Z.Modules} (e : E ≅ F) (W : Z.Opens) (y : Γ(F, W)) :
    e.hom.app W (e.inv.app W y) = y :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ W y) e.inv_hom_id

/-- The comparison only depends on the isomorphism class of the module. -/
public theorem IsSectionsComplete.of_iso {E F : Z.Modules} (e : E ≅ F)
    (h : T.IsSectionsComplete E) : T.IsSectionsComplete F where
  exists_section := by
    intro s hs
    obtain ⟨W, hW, t, ht⟩ := h.exists_section
      (fun n => ((Scheme.Modules.pullback (T.obj n).hom).map e.inv).app ⊤ (s n))
      (T.isCompatible_map e.inv hs)
    refine ⟨W, hW, e.hom.app W t, fun n => ?_⟩
    refine (T.sectionsAt_natural e.hom hW n t).trans ?_
    refine (congrArg
      (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map e.hom).app ⊤ v) (ht n)).trans ?_
    exact app_pullback_map_inv_hom (T.obj n).hom e (s n)
  eq_of_sectionsAt_eq := by
    intro W W' hW hW' t u htu
    obtain ⟨W'', hW'', h₁, h₂, hres⟩ := h.eq_of_sectionsAt_eq W W' hW hW'
      (e.inv.app W t) (e.inv.app W' u) (fun n => by
        refine (T.sectionsAt_natural e.inv hW n t).trans ?_
        refine Eq.trans ?_ (T.sectionsAt_natural e.inv hW' n u).symm
        exact congrArg
          (fun v => ((Scheme.Modules.pullback (T.obj n).hom).map e.inv).app ⊤ v) (htu n))
    refine ⟨W'', hW'', h₁, h₂, ?_⟩
    have key : ∀ (V : Z.Opens) (h : W'' ≤ V) (y : Γ(F, V)),
        e.hom.app W'' (E.presheaf.map (homOfLE h).op (e.inv.app V y)) =
          F.presheaf.map (homOfLE h).op y := fun V h y =>
      (NatTrans.naturality_apply e.hom.mapPresheaf (homOfLE h).op (e.inv.app V y)).trans
        (congrArg (fun v => F.presheaf.map (homOfLE h).op v) (app_inv_hom e V y))
    exact (key W h₁ t).symm.trans
      ((congrArg (fun v => Scheme.Modules.Hom.app e.hom W'' v) hres).trans (key W' h₂ u))

end InfinitesimalTower

/-! ### The tower of infinitesimal neighbourhoods read over an open neighbourhood -/

variable {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- A morphism into `X` whose image lies in an open `V` factors through `V`, uniquely. -/
public theorem existsUnique_lift {Z : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
    (hV : Set.range f.base ⊆ V) : ∃! g : Z ⟶ V.toScheme, g ≫ V.ι = f :=
  have hV' : Set.range f.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hV
  ⟨IsOpenImmersion.lift V.ι f hV', IsOpenImmersion.lift_fac _ _ _, fun g hg =>
    (cancel_mono V.ι).1 (hg.trans (IsOpenImmersion.lift_fac V.ι f hV').symm)⟩

/-- The factorization of a morphism through an open containing its image. -/
public def liftToOpen {Z : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens) (hV : Set.range f.base ⊆ V) :
    Z ⟶ V.toScheme :=
  (existsUnique_lift f V hV).exists.choose

/-- The factorization composes back to the original morphism. -/
public theorem liftToOpen_ι {Z : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
    (hV : Set.range f.base ⊆ V) : liftToOpen f V hV ≫ V.ι = f :=
  (existsUnique_lift f V hV).exists.choose_spec

/-- The closed immersion into an open neighbourhood induced by a closed immersion. -/
public def nbhdImmersion (V : X.Opens) (hV : Set.range i.base ⊆ V) : Y ⟶ V.toScheme :=
  liftToOpen i V hV

omit [IsClosedImmersion i] in
/-- The induced immersion composes back to the original one. -/
public theorem nbhdImmersion_ι (V : X.Opens) (hV : Set.range i.base ⊆ V) :
    nbhdImmersion i V hV ≫ V.ι = i :=
  liftToOpen_ι i V hV

/-- An open neighbourhood of `Y` contains every infinitesimal neighbourhood of `Y`. -/
public theorem range_nthInfinitesimalNeighbourhoodι_subset (V : X.Opens)
    (hV : Set.range i.base ⊆ V) (n : ℕ) :
    Set.range (nthInfinitesimalNeighbourhoodι i n).base ⊆ V := by
  rw [range_nthInfinitesimalNeighbourhoodι]; exact hV

/-- The `n`-th infinitesimal neighbourhood of `Y` in `X`, as a scheme over an open neighbourhood
`V` of `Y`. -/
public def nbhdOver (V : X.Opens) (hV : Set.range i.base ⊆ V) (n : ℕ) : Over V.toScheme :=
  Over.mk (liftToOpen (nthInfinitesimalNeighbourhoodι i n) V
    (range_nthInfinitesimalNeighbourhoodι_subset i V hV n))

/-- The structure morphism of the lifted tower composes back to the one over `X`. -/
public theorem nbhdOver_hom_ι (V : X.Opens) (hV : Set.range i.base ⊆ V) (n : ℕ) :
    (nbhdOver i V hV n).hom ≫ V.ι = nthInfinitesimalNeighbourhoodι i n :=
  liftToOpen_ι (nthInfinitesimalNeighbourhoodι i n) V
    (range_nthInfinitesimalNeighbourhoodι_subset i V hV n)

/-- Each term of the lifted tower has the image of the induced immersion. -/
public theorem range_nbhdOver_hom (V : X.Opens) (hV : Set.range i.base ⊆ V) (n : ℕ) :
    Set.range (nbhdOver i V hV n).hom.base = Set.range (nbhdImmersion i V hV).base := by
  have hinj : Function.Injective V.ι.base := V.ι.isOpenEmbedding.injective
  apply hinj.image_injective
  rw [← Set.range_comp, ← Set.range_comp]
  have h₁ : V.ι.base ∘ (nbhdOver i V hV n).hom.base =
      (nthInfinitesimalNeighbourhoodι i n).base := by
    rw [← TopCat.coe_comp, ← Scheme.Hom.comp_base, nbhdOver_hom_ι]
    rfl
  have h₂ : V.ι.base ∘ (nbhdImmersion i V hV).base = i.base := by
    rw [← TopCat.coe_comp, ← Scheme.Hom.comp_base, nbhdImmersion_ι]
  rw [h₁, h₂]
  exact range_nthInfinitesimalNeighbourhoodι i n

/-- The inclusions of the tower over `X` are morphisms of schemes over `V`. -/
public theorem nbhdTransition_w (V : X.Opens) (hV : Set.range i.base ⊆ V) {n m : ℕ} (h : n ≤ m) :
    (show nthInfinitesimalNeighbourhood i n ⟶ nthInfinitesimalNeighbourhood i m from
        (nthInfinitesimalNeighbourhoodTransition i h).left) ≫ (nbhdOver i V hV m).hom =
      (nbhdOver i V hV n).hom :=
  (cancel_mono V.ι).1
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (nthInfinitesimalNeighbourhoodTransition i h).left ≫ k)
          (nbhdOver_hom_ι i V hV m)).trans
        ((Over.w (nthInfinitesimalNeighbourhoodTransition i h)).trans
          (nbhdOver_hom_ι i V hV n).symm)))

/-- The transition morphisms of the lifted tower. -/
public def nbhdTransition (V : X.Opens) (hV : Set.range i.base ⊆ V) {n m : ℕ} (h : n ≤ m) :
    nbhdOver i V hV n ⟶ nbhdOver i V hV m :=
  Over.homMk
    (show nthInfinitesimalNeighbourhood i n ⟶ nthInfinitesimalNeighbourhood i m from
      (nthInfinitesimalNeighbourhoodTransition i h).left)
    (nbhdTransition_w i V hV h)

/-- The infinitesimal neighbourhoods of `Y` in `X`, as a tower over an open neighbourhood `V`. -/
public def nbhdTower (V : X.Opens) (hV : Set.range i.base ⊆ V) :
    InfinitesimalTower V.toScheme where
  obj n := nbhdOver i V hV n
  trans _ _ h := nbhdTransition i V hV h
  support := Set.range (nbhdImmersion i V hV).base
  range_hom_subset n := (range_nbhdOver_hom i V hV n).le

/-- **Condition (3) of [Stacks, Tag 0EK2] for one module.** The colimit of the sections of `E`
over the open neighbourhoods of `Y` inside `V` is the inverse limit of the sections of `E` on the
infinitesimal neighbourhoods of `Y`. -/
public abbrev IsNeighbourhoodSectionsCompleteOn (V : X.Opens) (hV : Set.range i.base ⊆ V)
    (E : V.toScheme.Modules) : Prop :=
  (nbhdTower i V hV).IsSectionsComplete E

/-- The infinitesimal neighbourhoods of `Y`, as a tower over `X` itself. -/
public def infTower : InfinitesimalTower X where
  obj n := nthInfinitesimalNeighbourhoodOver i n
  trans _ _ h := nthInfinitesimalNeighbourhoodTransition i h
  support := Set.range i.base
  range_hom_subset n := (range_nthInfinitesimalNeighbourhoodι i n).le

/-- The comparison at the tower over `X` is the one of
`Stacks.Algebraization.IsNeighbourhoodSectionsComplete`. -/
public theorem infTower_isSectionsComplete_iff (F : X.Modules) :
    (infTower i).IsSectionsComplete F ↔ IsNeighbourhoodSectionsComplete i F :=
  ⟨fun h => ⟨h.exists_section, h.eq_of_sectionsAt_eq⟩, fun h => ⟨h.1, h.2⟩⟩

end Stacks.Algebraization

end
