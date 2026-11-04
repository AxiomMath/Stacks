module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.OpenPushRestrictBaseChange

/-!
# Base change of the extended alternating Čech complex of global equations

Let `g : X' ⟶ X` be a morphism of schemes, let `f : Fin c → Γ(X, 𝒪_X)` be a finite family of
global functions, write `f'ᵢ = g^♯(fᵢ)` for the pulled-back equations, and let `ℱ` be an
`𝒪_X`-module.  The principal-open intersections of Tag 0G7I are compatible with inverse images,
`g^{-1}(U_{i₀…i_p}) = U'_{i₀…i_p}`, so the two extended alternating Čech complexes of Tag 0G7I
— the one of `ℱ` for `f` and the one of `g^*ℱ` for `f'` — are comparable, and this file builds
the comparison

`g^*(ℱ^•) ⟶ (g^*ℱ)^•`

of [Stacks, Tag 0G7U], degreewise and as a map of complexes, both in the `ℕ`-grading the
complex is constructed in and in the `ℤ`-grading obtained by extending it by zero.

In degree `0` the comparison is the identity, because both complexes have the coefficient module
itself there.  In degree `p + 1` it is the product over the strictly increasing `(p+1)`-tuples of
the termwise comparison

`g^*(j_{U,*}(ℱ|_U)) ⟶ j_{U',*}((g^*ℱ)|_{U'})`, `U = U_{i₀…i_p}`, `U' = g^{-1}(U)`,

which is `Stacks.Perfect.OpenPushRestrictBaseChange.openBaseChange` read through the two
comparison isomorphisms `toRPhom`/`toRPinv` between the `restrictFunctor` model of the Čech term
and the `pullback` model it is defined by, and transported along `g^{-1}(U_{i₀…i_p}) =
U'_{i₀…i_p}`.

## Main definitions

* `Stacks.Perfect.CechBaseChange.restrictedModuleBaseChange`: the termwise comparison.
* `Stacks.Perfect.CechBaseChange.prodTermBaseChange`: its product over the tuples of a fixed
  length, i.e. the comparison in a positive degree.
* `Stacks.Perfect.CechBaseChange.cplxBaseChange`: the comparison of complexes in the
  `ℕ`-grading.
* `Stacks.Perfect.CechBaseChange.extendBaseChange`: the comparison of complexes in the
  `ℤ`-grading, obtained from the previous one by extending by zero.

## Main results

* `restrictedModuleBaseChange_augR`: the termwise comparison is compatible with the
  augmentations `ℱ ⟶ j_{U,*}(ℱ|_U)`, which is the degree-`0` differential of the Čech complex.
* `restrictedModuleBaseChange_canR`: the termwise comparison is compatible with the canonical
  restrictions `j_{U,*}(ℱ|_U) ⟶ j_{V,*}(ℱ|_V)` for `V ≤ U`, out of which the higher
  differentials are built.
* `restrictedModuleBaseChange_naturality`: the termwise comparison is natural in the coefficient
  module.
* `cplxBaseChange_f_zero` and `cplxBaseChange_f_succ_pi`: the degreewise description of the
  comparison of complexes.
* `cplxBaseChange_naturality`: the comparison of complexes is natural in the coefficient module.

## Implementation notes

The two previous results are used exactly once each: `openBaseChange_unit` gives
`restrictedModuleBaseChange_augR`, `openBaseChange_canPR` gives
`restrictedModuleBaseChange_canR`, and `openBaseChange_naturality` gives
`restrictedModuleBaseChange_naturality`.  Each time the `toRPhom`/`toRPinv` pair sitting around
the `openBaseChange` cancels by `toRPhom_toRPinv`, and the transport along the equality of index
opens is moved across the other arrow by one of the three `eqToHom` transport lemmas proved
first; the only one of those that is not a `subst` is
`Stacks.Perfect.ExtendedAlternatingCech.mapR`-vs-`toRPhom`, which is `mapR_toRPinv` with the
comparison isomorphisms cancelled on the other side (`pushRestrictMap_toRPhom`).

`equationsOpen_pullback`, the equality of index opens, is stated here as well as in
`EquationsBaseChange` because it has to be stated for the `equationsOpen` of
`Stacks.Perfect.ExtendedAlternatingCech`, which is the one the Čech complex of this file is
built from: `rw` and `simp only` match at `instances` transparency, so
`AlgebraicGeometry.ExtendedAlternatingCech.equationsOpen_pullback`, stated for the same
definition in the other of the two namespaces that carry it, never fires on these goals.  Which
of the two it is about is the whole content of the distinction, so the statement here writes
`Stacks.Perfect.ExtendedAlternatingCech.equationsOpen` out in full instead of leaning on the
`open` above.

Both the degree-`0` and the degree-`(p+1)` squares land in a categorical product, so they are
checked componentwise with `CategoryTheory.Limits.Pi.hom_ext`; the alternating sum of the higher
differential is distributed over composition with `Preadditive.sum_comp`, `Preadditive.comp_sum`
and `CategoryTheory.Functor.map_sum`, which is available because `Scheme.Modules.pullback g` is
additive.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeMayerVietoris (pushRestrict)
open Stacks.Perfect.OpenPushRestrictBaseChange (openBaseChange openBaseChange_unit
  openBaseChange_canPR openBaseChange_naturality)
open Stacks.Perfect.ExtendedAlternatingCech (equationsOpen restrictedModule toRPhom toRPinv
  toRPhom_toRPinv toRPinv_toRPhom canPR mapR mapR_toRPinv prodTerm canR augR difZero difSucc
  cplx cplx_d_zero cplx_d_succ cplxMap prodMap prodMap_π omitLe)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechBaseChange

/-! ### Transport of the three canonical maps along an equality of opens -/

/-- **Transport of the unit of a restriction adjunction along an equality of opens.** -/
public theorem unit_comp_eqToHom_pushRestrict {Y : Scheme.{u}} (G : Y.Modules)
    {A B : Y.Opens} (h : A = B) :
    (Scheme.Modules.restrictAdjunction A.ι).unit.app G ≫
        eqToHom (congrArg (pushRestrict G) h) =
      (Scheme.Modules.restrictAdjunction B.ι).unit.app G := by
  subst h
  rw [eqToHom_refl, Category.comp_id]

/-- **Transport of a canonical restriction `canPR` along equalities of its two opens.** -/
public theorem canPR_comp_eqToHom_pushRestrict {Y : Scheme.{u}} (G : Y.Modules)
    {A B A' B' : Y.Opens} (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B') :
    canPR G hAB ≫ eqToHom (congrArg (pushRestrict G) hA) =
      eqToHom (congrArg (pushRestrict G) hB) ≫ canPR G hAB' := by
  subst hA
  subst hB
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **Transport of the direct image of a restricted morphism along an equality of opens.** -/
public theorem map_comp_eqToHom_pushRestrict {Y : Scheme.{u}} {G H : Y.Modules} (φ : G ⟶ H)
    {A B : Y.Opens} (h : A = B) :
    (Scheme.Modules.pushforward A.ι).map ((Scheme.Modules.restrictFunctor A.ι).map φ) ≫
        eqToHom (congrArg (pushRestrict H) h) =
      eqToHom (congrArg (pushRestrict G) h) ≫
        (Scheme.Modules.pushforward B.ι).map ((Scheme.Modules.restrictFunctor B.ι).map φ) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-! ### The index opens of the pulled-back equations -/

/-- **The principal-open intersection of the pulled-back equations is the inverse image of the
principal-open intersection of the equations.**  Inverse image commutes with the finite
intersection by `AlgebraicGeometry.ExtendedAlternatingCech.preimage_iInf`, and with each
principal open by `AlgebraicGeometry.Scheme.preimage_basicOpen`.

The `equationsOpen` of the statement is written out in full: it is the one of
`Stacks.Perfect.ExtendedAlternatingCech`, and that is the whole point of the lemma. -/
public theorem equationsOpen_pullback (p : ℕ) (s : CechCochains.OrdIndex (I := Fin c) p) :
    g ⁻¹ᵁ Stacks.Perfect.ExtendedAlternatingCech.equationsOpen f p s =
      Stacks.Perfect.ExtendedAlternatingCech.equationsOpen
        (fun j => g.appTop (f j)) p s := by
  simp only [equationsOpen, AlgebraicGeometry.ExtendedAlternatingCech.preimage_iInf]
  exact iInf_congr fun k => Scheme.preimage_basicOpen g _

/-- **An inclusion of principal-open intersections survives the base change.** -/
public theorem equationsOpen_pullback_mono {p q : ℕ}
    {s : CechCochains.OrdIndex (I := Fin c) p} {t : CechCochains.OrdIndex (I := Fin c) q}
    (h : equationsOpen f q t ≤ equationsOpen f p s) :
    equationsOpen (fun j => g.appTop (f j)) q t ≤
      equationsOpen (fun j => g.appTop (f j)) p s := by
  rw [← equationsOpen_pullback g f q t, ← equationsOpen_pullback g f p s]
  exact Scheme.Hom.preimage_mono g h

/-! ### The comparison `toRPhom` is natural in the coefficient module -/

/-- **The comparison from the `restrictFunctor` model of a Čech term to its `pullback` model is
natural in the coefficient module.**  This is `mapR_toRPinv` with the two comparison
isomorphisms cancelled on the other side. -/
public theorem pushRestrictMap_toRPhom {F G : X.Modules} (φ : F ⟶ G) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.pushforward (equationsOpen f p s).ι).map
          ((Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).map φ) ≫
        toRPhom f G p s =
      toRPhom f F p s ≫ mapR f φ p s := by
  have key : toRPhom f F p s ≫ mapR f φ p s ≫ toRPinv f G p s =
      (Scheme.Modules.pushforward (equationsOpen f p s).ι).map
        ((Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).map φ) := by
    rw [mapR_toRPinv, ← Category.assoc, toRPhom_toRPinv, Category.id_comp]
  rw [← key, Category.assoc, Category.assoc, toRPinv_toRPhom, Category.comp_id]

/-! ### The termwise comparison -/

/-- **The termwise base-change comparison `g^*(j_{U,*}(ℱ|_U)) ⟶ j_{U',*}((g^*ℱ)|_{U'})` of the
Čech terms of [Stacks, Tag 0G7U].**  It passes to the `restrictFunctor` model with `toRPinv`,
base-changes there with `openBaseChange`, transports along the equality of index opens, and
comes back with `toRPhom`. -/
public def restrictedModuleBaseChange (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.pullback g).obj (restrictedModule f F p s) ⟶
      restrictedModule (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p s :=
  (Scheme.Modules.pullback g).map (toRPinv f F p s) ≫
    openBaseChange g F (equationsOpen f p s) ≫
    eqToHom (congrArg (pushRestrict ((Scheme.Modules.pullback g).obj F))
      (equationsOpen_pullback g f p s)) ≫
    toRPhom (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p s

/-- The pullback of `toRPhom` followed by the pullback of `toRPinv` is the identity. -/
private theorem map_toRPhom_comp_map_toRPinv (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.pullback g).map (toRPhom f F p s) ≫
      (Scheme.Modules.pullback g).map (toRPinv f F p s) = 𝟙 _ := by
  rw [← Functor.map_comp, toRPhom_toRPinv, CategoryTheory.Functor.map_id]

/-- **The termwise comparison is compatible with the augmentations.**  This is the degree-`0`
differential of the extended alternating Čech complex, and the statement is
`openBaseChange_unit` after the `toRPhom`/`toRPinv` pair has cancelled. -/
public theorem restrictedModuleBaseChange_augR (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.pullback g).map (augR f F p s) ≫ restrictedModuleBaseChange g f F p s =
      augR (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p s := by
  simp only [restrictedModuleBaseChange, augR, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_toRPhom_comp_map_toRPinv g f F p s),
    reassoc_of% (openBaseChange_unit g F (equationsOpen f p s)),
    reassoc_of% (unit_comp_eqToHom_pushRestrict ((Scheme.Modules.pullback g).obj F)
      (equationsOpen_pullback g f p s))]

/-- **The termwise comparison is compatible with the canonical restrictions between the Čech
terms of two nested index opens.**  These are the maps the higher differentials of the extended
alternating Čech complex are assembled from, and the statement is `openBaseChange_canPR` after
the `toRPhom`/`toRPinv` pairs have cancelled. -/
public theorem restrictedModuleBaseChange_canR (F : X.Modules) {p q : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) (t : CechCochains.OrdIndex (I := Fin c) q)
    (h : equationsOpen f q t ≤ equationsOpen f p s)
    (h' : equationsOpen (fun j => g.appTop (f j)) q t ≤
      equationsOpen (fun j => g.appTop (f j)) p s) :
    (Scheme.Modules.pullback g).map (canR f F s t h) ≫ restrictedModuleBaseChange g f F q t =
      restrictedModuleBaseChange g f F p s ≫
        canR (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) s t h' := by
  simp only [restrictedModuleBaseChange, canR, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_toRPhom_comp_map_toRPinv g f F q t),
    reassoc_of% (openBaseChange_canPR g F h),
    reassoc_of% (canPR_comp_eqToHom_pushRestrict ((Scheme.Modules.pullback g).obj F)
      (equationsOpen_pullback g f q t) (equationsOpen_pullback g f p s)
      (Scheme.Hom.preimage_mono g h) h'),
    reassoc_of% (toRPhom_toRPinv (fun j => g.appTop (f j))
      ((Scheme.Modules.pullback g).obj F) p s)]

/-- **The termwise comparison is natural in the coefficient module.** -/
public theorem restrictedModuleBaseChange_naturality {F G : X.Modules} (φ : F ⟶ G) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (Scheme.Modules.pullback g).map (mapR f φ p s) ≫ restrictedModuleBaseChange g f G p s =
      restrictedModuleBaseChange g f F p s ≫
        mapR (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).map φ) p s := by
  have hL : (Scheme.Modules.pullback g).map (mapR f φ p s) ≫
      (Scheme.Modules.pullback g).map (toRPinv f G p s) =
      (Scheme.Modules.pullback g).map (toRPinv f F p s) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pushforward (equationsOpen f p s).ι).map
            ((Scheme.Modules.restrictFunctor (equationsOpen f p s).ι).map φ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, mapR_toRPinv]
  simp only [restrictedModuleBaseChange, Category.assoc]
  rw [reassoc_of% hL, reassoc_of% (openBaseChange_naturality g (equationsOpen f p s) φ),
    reassoc_of% (map_comp_eqToHom_pushRestrict ((Scheme.Modules.pullback g).map φ)
      (equationsOpen_pullback g f p s)),
    pushRestrictMap_toRPhom]

/-! ### The comparison in a positive degree -/

/-- **The base-change comparison of the degree-`(p+1)` terms of the extended alternating Čech
complex**: the product of the termwise comparisons over the strictly increasing
`(p+1)`-tuples. -/
public def prodTermBaseChange (F : X.Modules) (p : ℕ) :
    (Scheme.Modules.pullback g).obj (prodTerm f F p) ⟶
      prodTerm (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p :=
  Pi.lift fun s : CechCochains.OrdIndex (I := Fin c) p =>
    (Scheme.Modules.pullback g).map
        (Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u) s) ≫
      restrictedModuleBaseChange g f F p s

/-- The components of `prodTermBaseChange` are the termwise comparisons. -/
public theorem prodTermBaseChange_π (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    prodTermBaseChange g f F p ≫
        Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p =>
          restrictedModule (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p u) s =
      (Scheme.Modules.pullback g).map
          (Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u) s) ≫
        restrictedModuleBaseChange g f F p s :=
  Limits.Pi.lift_π _ s

/-- **The degree-`0` square of the comparison commutes.** -/
public theorem prodTermBaseChange_difZero (F : X.Modules) :
    (Scheme.Modules.pullback g).map (difZero f F) ≫ prodTermBaseChange g f F 0 =
      difZero (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) := by
  refine Limits.Pi.hom_ext _ _ fun s => ?_
  have hd : difZero f F ≫
      Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) 0 => restrictedModule f F 0 u) s =
      augR f F 0 s := Limits.Pi.lift_π _ s
  have hmap := congrArg (Scheme.Modules.pullback g).map hd
  rw [Functor.map_comp] at hmap
  rw [Category.assoc, prodTermBaseChange_π, ← Category.assoc, hmap,
    restrictedModuleBaseChange_augR]
  exact (Limits.Pi.lift_π _ s).symm

/-- The components of `difSucc` are the alternating sums of the restrictions of the components
in the previous degree. -/
private theorem difSucc_π (F : X.Modules) (p : ℕ) (t : CechCochains.OrdIndex (I := Fin c) (p + 1)) :
    difSucc f F p ≫
      Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) (p + 1) =>
        restrictedModule f F (p + 1) u) t =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u)
            ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩ ≫
          canR f F _ t (omitLe f t j)) :=
  Limits.Pi.lift_π _ t

/-- **The degree-`(p+1)` square of the comparison commutes.** -/
public theorem prodTermBaseChange_difSucc (F : X.Modules) (p : ℕ) :
    (Scheme.Modules.pullback g).map (difSucc f F p) ≫ prodTermBaseChange g f F (p + 1) =
      prodTermBaseChange g f F p ≫
        difSucc (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p := by
  refine Limits.Pi.hom_ext _ _ fun t => ?_
  have hmap := congrArg (Scheme.Modules.pullback g).map (difSucc_π f F p t)
  rw [Functor.map_comp, Functor.map_sum] at hmap
  simp only [Functor.map_zsmul, Functor.map_comp] at hmap
  rw [Category.assoc, prodTermBaseChange_π, ← Category.assoc, hmap, Preadditive.sum_comp,
    Category.assoc,
    difSucc_π (fun i => g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) p t,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [Category.assoc, restrictedModuleBaseChange_canR g f F _ t (omitLe f t j)
      (omitLe (fun i => g.appTop (f i)) t j), ← Category.assoc, ← prodTermBaseChange_π,
    Category.assoc]

/-- **The comparison is natural in the coefficient module in a positive degree.** -/
public theorem prodTermBaseChange_naturality {F G : X.Modules} (φ : F ⟶ G) (p : ℕ) :
    (Scheme.Modules.pullback g).map (prodMap f φ p) ≫ prodTermBaseChange g f G p =
      prodTermBaseChange g f F p ≫
        prodMap (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).map φ) p := by
  refine Limits.Pi.hom_ext _ _ fun s => ?_
  have hL := congrArg (Scheme.Modules.pullback g).map (prodMap_π f φ p s)
  rw [Functor.map_comp, Functor.map_comp] at hL
  simp only [Category.assoc]
  rw [prodMap_π, reassoc_of% (prodTermBaseChange_π g f F p s), prodTermBaseChange_π g f G p s,
    reassoc_of% hL, restrictedModuleBaseChange_naturality]

/-! ### The comparison of complexes -/

/-- The degreewise base-change comparison of the extended alternating Čech complexes: the
identity in degree `0`, and the product of the termwise comparisons in degree `p + 1`. -/
public def cplxBaseChangeF (F : X.Modules) : ∀ n : ℕ,
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cplx f F)).X n ⟶
      (cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).X n
  | 0 => 𝟙 _
  | (p + 1) => prodTermBaseChange g f F p

/-- **The base-change comparison `g^*(ℱ^•) ⟶ (g^*ℱ)^•` of the extended alternating Čech
complexes of [Stacks, Tag 0G7U], in the `ℕ`-grading.** -/
public def cplxBaseChange (F : X.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cplx f F) ⟶
      cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) where
  f := cplxBaseChangeF g f F
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    cases i with
    | zero =>
      rw [show (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (cplx f F)).d 0 (0 + 1) = (Scheme.Modules.pullback g).map (difZero f F) from
          congrArg (Scheme.Modules.pullback g).map (cplx_d_zero f F),
        show (cplx (fun i => g.appTop (f i)) ((Scheme.Modules.pullback g).obj F)).d 0 (0 + 1) =
            difZero (fun i => g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) from
          cplx_d_zero _ _]
      exact (Category.id_comp _).trans (prodTermBaseChange_difZero g f F).symm
    | succ p =>
      rw [show (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (cplx f F)).d (p + 1) (p + 1 + 1) =
            (Scheme.Modules.pullback g).map (difSucc f F p) from
          congrArg (Scheme.Modules.pullback g).map (cplx_d_succ f F p),
        show (cplx (fun i => g.appTop (f i)) ((Scheme.Modules.pullback g).obj F)).d
            (p + 1) (p + 1 + 1) =
            difSucc (fun i => g.appTop (f i)) ((Scheme.Modules.pullback g).obj F) p from
          cplx_d_succ _ _ p]
      exact (prodTermBaseChange_difSucc g f F p).symm

/-- **In degree `0` the comparison of complexes is the identity**, both complexes having the
coefficient module itself there. -/
public theorem cplxBaseChange_f_zero (F : X.Modules) : (cplxBaseChange g f F).f 0 = 𝟙 _ := rfl

/-- **In positive degrees the comparison of complexes is the product of the termwise
comparisons.** -/
public theorem cplxBaseChange_f_succ_pi (F : X.Modules) (p : ℕ)
    (s : CechCochains.OrdIndex (I := Fin c) p) :
    (cplxBaseChange g f F).f (p + 1) ≫
        Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p =>
          restrictedModule (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) p u) s =
      (Scheme.Modules.pullback g).map
          (Pi.π (fun u : CechCochains.OrdIndex (I := Fin c) p => restrictedModule f F p u) s) ≫
        restrictedModuleBaseChange g f F p s :=
  prodTermBaseChange_π g f F p s

/-- **The base-change comparison of the extended alternating Čech complexes, extended by zero to
the `ℤ`-grading.** -/
public def extendBaseChange (F : X.Modules) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((cplx f F).extend ComplexShape.embeddingUpNat) ⟶
      (cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).extend
        ComplexShape.embeddingUpNat :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g) (cplx f F)
      ComplexShape.embeddingUpNat).inv ≫
    HomologicalComplex.extendMap (cplxBaseChange g f F) ComplexShape.embeddingUpNat

/-- **The comparison of complexes is natural in the coefficient module.** -/
public theorem cplxBaseChange_naturality {F G : X.Modules} (φ : F ⟶ G) :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).map (cplxMap f φ) ≫
        cplxBaseChange g f G =
      cplxBaseChange g f F ≫
        cplxMap (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).map φ) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ p => exact prodTermBaseChange_naturality g f φ p

end Stacks.Perfect.CechBaseChange

end
