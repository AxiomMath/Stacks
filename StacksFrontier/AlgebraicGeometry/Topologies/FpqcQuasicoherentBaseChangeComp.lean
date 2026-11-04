module

public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore

/-!
# Base change of the presheaf of Tag 03DS along a composite

`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` identifies the restriction of the presheaf of
**Stacks 03DS** of a quasi-coherent module `𝓕` on `U` along `CategoryTheory.Over.map g`, for a
morphism `g : W ⟶ U`, with the presheaf of Stacks 03DS of `g^*𝓕`. This file proves its
compatibility with *composition of base changes*: for a second morphism `k : W' ⟶ W`, base
changing along `g` and then along `k` is base changing along `k ≫ g`, the two sides being
compared by the composition isomorphism `k^*(g^*𝓕) ≅ (k ≫ g)^*𝓕` of the pullback pseudofunctor.

## Main definitions

* `Stacks.Sites.pullbackCompSectionsIso`: the composition isomorphism of the pullback
  pseudofunctor, on the global sections of a twofold pullback -- the comparison between the
  values at one object of the two presheaves of Stacks 03DS that a composite base change
  produces.
* `Stacks.Sites.baseChangeCompIso`: the right-hand identification of the composition square as a
  single isomorphism, base change along `k ≫ g` followed by that comparison read backwards.

## Main results

* `Stacks.Sites.pullbackComp_inv_assoc_app`: the associativity coherence of the pullback
  pseudofunctor in the inverse direction.
* `Stacks.Sites.baseChangeSectionsIso_comp`: **base change along `g` followed by base change
  along `k` is base change along `k ≫ g`**, on global sections.
* `Stacks.Sites.quasiCoherentPresheafBaseChangeIso_comp`: the same for
  `Stacks.Sites.quasiCoherentPresheafBaseChangeIso`.
* `Stacks.Sites.baseChangeIso_hom_comp_restriction`: the composition compatibility paired with
  the naturality, as one square: an arrow of the slice over `W` lying over `k` is carried by the
  base-change identifications to the restriction map of the presheaf of Stacks 03DS of `𝓕`
  itself.
* `Stacks.Sites.baseChangeCompIso_hom_comp_restriction`: the same square with the right-hand
  identification packaged as `Stacks.Sites.baseChangeCompIso`.
* `Stacks.Sites.baseChangeCompIso_inv_restriction`: the square read backwards through the two
  base-change identifications and through arrows identifying the slice objects with `W / U` and
  `W' / U`.
* `Stacks.Sites.pullbackSectionsMap_congr_source`: a restriction map of the presheaf of
  Stacks 03DS depends on its arrow only through the underlying morphism of schemes.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Sites

/-! ### The associativity coherence in the inverse direction -/

/-- **The associativity coherence of the pullback pseudofunctor, in the inverse direction.** The
two ways of identifying `(a ≫ k ≫ g)^*𝓕` with `a^*k^*g^*𝓕` through the inverses of the
composition isomorphisms agree. -/
theorem pullbackComp_inv_assoc_app {A U W W' : Scheme.{u}} (a : A ⟶ W') (k : W' ⟶ W) (g : W ⟶ U)
    (𝓕 : U.Modules) :
    (Scheme.Modules.pullbackCongr (Category.assoc a k g).symm).hom.app 𝓕 ≫
        (Scheme.Modules.pullbackComp (a ≫ k) g).inv.app 𝓕 ≫
        (Scheme.Modules.pullbackComp a k).inv.app ((Scheme.Modules.pullback g).obj 𝓕) =
      (Scheme.Modules.pullbackComp a (k ≫ g)).inv.app 𝓕 ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp k g).inv.app 𝓕) := by
  have h1 : (Scheme.Modules.pullbackComp a (k ≫ g)).inv.app 𝓕 ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp k g).inv.app 𝓕) ≫
        (Scheme.Modules.pullbackComp a k).hom.app ((Scheme.Modules.pullback g).obj 𝓕) =
      (Scheme.Modules.pullbackCongr (Category.assoc a k g).symm).hom.app 𝓕 ≫
        (Scheme.Modules.pullbackComp (a ≫ k) g).inv.app 𝓕 := by
    rw [pullbackComp_assoc_app a k g 𝓕, Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h1]
  simp

/-! ### The composition isomorphism on global sections -/

section Comp

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) (g : W ⟶ U) (k : W' ⟶ W)

/-- **The composition isomorphism of the pullback pseudofunctor, on global sections.**  For an
object `A / W'` it compares the value at `A` of the presheaf of Stacks 03DS of `k^*(g^*𝓕)` with
the value at `A` of the presheaf of Stacks 03DS of `(k ≫ g)^*𝓕`: the two modules that base
changing `𝓕` along `g` and then along `k`, respectively along `k ≫ g`, produce on `W'`. -/
noncomputable def pullbackCompSectionsIso (A : Over W') :
    Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback k).obj
        ((Scheme.Modules.pullback g).obj 𝓕)), ⊤) ≅
      Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback (k ≫ g)).obj 𝓕), ⊤) :=
  sectionsTopIso ((Scheme.Modules.pullback A.hom).mapIso
    ((Scheme.Modules.pullbackComp k g).app 𝓕))

/-- The forward map of `Stacks.Sites.pullbackCompSectionsIso` is the map on global sections of
the pullback along `A.hom` of the composition isomorphism. -/
@[simp]
lemma pullbackCompSectionsIso_hom (A : Over W') :
    (pullbackCompSectionsIso 𝓕 g k A).hom =
      ((Scheme.Modules.pullback A.hom).map
        ((Scheme.Modules.pullbackComp k g).hom.app 𝓕)).app ⊤ := rfl

/-- The inverse map of `Stacks.Sites.pullbackCompSectionsIso` is the map on global sections of
the pullback along `A.hom` of the inverse of the composition isomorphism. -/
@[simp]
lemma pullbackCompSectionsIso_inv (A : Over W') :
    (pullbackCompSectionsIso 𝓕 g k A).inv =
      ((Scheme.Modules.pullback A.hom).map
        ((Scheme.Modules.pullbackComp k g).inv.app 𝓕)).app ⊤ := rfl

/-- **Base change along `g` followed by base change along `k` is base change along `k ≫ g`.**
The two readings of the value at `A / W'` of the presheaf of Stacks 03DS of `𝓕` -- as the
sections over `A` of the twofold pullback `A.hom^*k^*g^*𝓕`, and as the sections over `A` of
`A.hom^*(k ≫ g)^*𝓕` -- differ by the composition isomorphism of the pullback pseudofunctor,
the sources being matched by the associativity of `A.hom`, `k` and `g`. -/
theorem baseChangeSectionsIso_comp (A : Over W') :
    (sectionsTopIso ((Scheme.Modules.pullbackCongr
          (Category.assoc A.hom k g).symm).app 𝓕)).hom ≫
        (baseChangeSectionsIso 𝓕 (Over.mk g) ((Over.map k).obj A)).hom ≫
        (baseChangeSectionsIso ((Scheme.Modules.pullback g).obj 𝓕) (Over.mk k) A).hom =
      (baseChangeSectionsIso 𝓕 (Over.mk (k ≫ g)) A).hom ≫
        (pullbackCompSectionsIso 𝓕 g k A).inv := by
  have key := pullbackComp_inv_assoc_app A.hom k g 𝓕
  simp only [sectionsTopIso_hom, baseChangeSectionsIso_hom, Iso.app_hom,
    pullbackCompSectionsIso_inv, ← Scheme.Modules.Hom.comp_app]
  exact congrArg (fun t => Scheme.Modules.Hom.app t ⊤) key

end Comp

/-! ### The same for the presheaf of Tag 03DS -/

section Presheaf

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) [𝓕.IsQuasicoherent] (g : W ⟶ U) (k : W' ⟶ W)

/-- The component at `A` of `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` is
`Stacks.Sites.baseChangeSectionsIso`. -/
lemma quasiCoherentPresheafBaseChangeIso_hom_app (A : Over W) :
    (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) =
      (baseChangeSectionsIso 𝓕 (Over.mk g) A).hom := rfl

/-- The component at `A` of the inverse of `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` is
the inverse of `Stacks.Sites.baseChangeSectionsIso`. -/
lemma quasiCoherentPresheafBaseChangeIso_inv_app (A : Over W) :
    (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).inv.app (op A) =
      (baseChangeSectionsIso 𝓕 (Over.mk g) A).inv := rfl

/-- **`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` is compatible with composition of base
changes.** -/
theorem quasiCoherentPresheafBaseChangeIso_comp (A : Over W') :
    (sectionsTopIso ((Scheme.Modules.pullbackCongr
          (Category.assoc A.hom k g).symm).app 𝓕)).hom ≫
        (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op ((Over.map k).obj A)) ≫
        (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
          (Over.mk k)).hom.app (op A) =
      (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk (k ≫ g))).hom.app (op A) ≫
        (pullbackCompSectionsIso 𝓕 g k A).inv :=
  baseChangeSectionsIso_comp 𝓕 g k A

end Presheaf

/-! ### The composition compatibility and the naturality, as one square -/

section Square

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) [𝓕.IsQuasicoherent] (g : W ⟶ U) (k : W' ⟶ W)

omit [𝓕.IsQuasicoherent] in
/-- `AlgebraicGeometry.pullbackSectionsMap` depends on its argument only through the underlying
morphism of schemes: two arrows of `Over U` with the same left component, whose sources are
`Over.mk c` and `Over.mk c'`, differ by the transport along `c = c'`. -/
theorem pullbackSectionsMap_congr_source {A₀ : Scheme.{u}} (Y : Over U) (j : A₀ ⟶ Y.left)
    {c c' : A₀ ⟶ U} (hc : j ≫ Y.hom = c) (hc' : j ≫ Y.hom = c') :
    pullbackSectionsMap 𝓕 (Over.homMk j hc' : Over.mk c' ⟶ Y) =
      pullbackSectionsMap 𝓕 (Over.homMk j hc : Over.mk c ⟶ Y) ≫
        ((Scheme.Modules.pullbackCongr (hc.symm.trans hc')).hom.app 𝓕).app ⊤ := by
  subst hc
  subst hc'
  simp [Scheme.Modules.pullbackCongr]

/-- An arrow `n : k^*A' ⟶ A` over `W` has underlying morphism over `U` along `g` and `k ≫ g`. -/
private theorem over_map_hom_w {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A) :
    n.left ≫ ((Over.map g).obj A).hom = A'.hom ≫ k ≫ g :=
  ((Category.assoc n.left A.hom g).symm.trans (congrArg (· ≫ g) (Over.w n))).trans
    (Category.assoc _ _ _)

/-- **The base-change identifications carry an arrow lying over `k` to a restriction map of the
presheaf of Stacks 03DS of `𝓕` itself.**  Let `A / W` and `A' / W'` be slice objects and let
`n : A' ⟶ A` be an arrow of the schemes over `W`, where `A'` is seen over `W` through `k`; let
`m` be the arrow of the schemes over `U` with the same underlying morphism of schemes. Then
restricting along `m` and then base changing along `k ≫ g` is base changing along `g`,
restricting along `n`, and base changing along `k`. -/
theorem baseChangeIso_hom_comp_restriction {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A)
    (m : (Over.map (k ≫ g)).obj A' ⟶ (Over.map g).obj A) (hm : m.left = n.left) :
    (quasiCoherentPresheafFunctor U 𝓕).map m.op ≫
        ((quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk (k ≫ g))).hom.app (op A') ≫
          (pullbackCompSectionsIso 𝓕 g k A').inv) =
      (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) ≫
        (quasiCoherentPresheafFunctor W ((Scheme.Modules.pullback g).obj 𝓕)).map n.op ≫
        (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
          (Over.mk k)).hom.app (op A') := by
  have hw := over_map_hom_w g k n
  have hw2 : n.left ≫ ((Over.map g).obj A).hom = (A'.hom ≫ k) ≫ g :=
    hw.trans (Category.assoc _ _ _).symm
  have e1 : m = (Over.homMk n.left hw : (Over.map (k ≫ g)).obj A' ⟶ (Over.map g).obj A) :=
    Over.OverMorphism.ext hm
  have e2 : (Over.map g).map n =
      (Over.homMk n.left hw2 :
        (Over.map g).obj ((Over.map k).obj A') ⟶ (Over.map g).obj A) :=
    Over.OverMorphism.ext rfl
  have h5 : (quasiCoherentPresheafFunctor U 𝓕).map m.op ≫
        (sectionsTopIso ((Scheme.Modules.pullbackCongr
          (Category.assoc A'.hom k g).symm).app 𝓕)).hom =
      (quasiCoherentPresheafFunctor U 𝓕).map ((Over.map g).map n).op := by
    rw [e1, e2]
    exact (pullbackSectionsMap_congr_source 𝓕 ((Over.map g).obj A) n.left hw hw2).symm
  have hnat := (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.naturality n.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, Over.mk_hom, Over.mk_left]
    at hnat
  refine (congrArg _ (quasiCoherentPresheafBaseChangeIso_comp 𝓕 g k A').symm).trans
    ((Category.assoc _ _ _).symm.trans ?_)
  rw [h5]
  exact ((reassoc_of% hnat) _).trans (Category.assoc _ _ _).symm

end Square

/-! ### The composition square with the two identifications packaged -/

section Tail

variable {U W W' : Scheme.{u}} (𝓕 : U.Modules) [𝓕.IsQuasicoherent] (g : W ⟶ U) (k : W' ⟶ W)

/-- **The right-hand identification of the composition square, as one isomorphism**: base change
along `k ≫ g`, followed by the composition isomorphism of the pullback pseudofunctor read
backwards, so that it lands in the value of the presheaf of Stacks 03DS of the twofold pullback
`k^*(g^*𝓕)` -- which is where base changing along `g` and then along `k` lands. -/
noncomputable def baseChangeCompIso (A' : Over W') :
    (quasiCoherentPresheafFunctor U 𝓕).obj (op ((Over.map (k ≫ g)).obj A')) ≅
      (quasiCoherentPresheafFunctor (Over.mk k).left
        ((Scheme.Modules.pullback (Over.mk k).hom).obj
          ((Scheme.Modules.pullback g).obj 𝓕))).obj (op A') :=
  (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk (k ≫ g))).app (op A') ≪≫
    (pullbackCompSectionsIso 𝓕 g k A').symm

/-- `Stacks.Sites.baseChangeIso_hom_comp_restriction` with the right-hand side of the square
read as the single isomorphism `Stacks.Sites.baseChangeCompIso`. -/
theorem baseChangeCompIso_hom_comp_restriction {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A)
    (m : (Over.map (k ≫ g)).obj A' ⟶ (Over.map g).obj A) (hm : m.left = n.left) :
    (quasiCoherentPresheafFunctor U 𝓕).map m.op ≫ (baseChangeCompIso 𝓕 g k A').hom =
      (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) ≫
        (quasiCoherentPresheafFunctor W ((Scheme.Modules.pullback g).obj 𝓕)).map n.op ≫
        (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
          (Over.mk k)).hom.app (op A') :=
  baseChangeIso_hom_comp_restriction 𝓕 g k n m hm

/-- The square of `Stacks.Sites.baseChangeCompIso_inv_restriction`, for an arrow `q` of the slice
over `U` equal to `e' ≫ m'`. -/
private theorem baseChangeCompIso_inv_restriction_aux {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A)
    (m' : (Over.map (k ≫ g)).obj A' ⟶ (Over.map g).obj A) (hm' : m'.left = n.left)
    (e' : (Over.mk (k ≫ g) : Over U) ⟶ (Over.map (k ≫ g)).obj A')
    (q : (Over.mk (k ≫ g) : Over U) ⟶ (Over.map g).obj A) (hq : q = e' ≫ m') :
    (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) ≫
        ((quasiCoherentPresheafFunctor W ((Scheme.Modules.pullback g).obj 𝓕)).map n.op ≫
          (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
            (Over.mk k)).hom.app (op A')) ≫
        ((baseChangeCompIso 𝓕 g k A').inv ≫ (quasiCoherentPresheafFunctor U 𝓕).map e'.op) =
      (quasiCoherentPresheafFunctor U 𝓕).map q.op := by
  have core := baseChangeCompIso_hom_comp_restriction 𝓕 g k n m' hm'
  simp only [Category.assoc] at core ⊢
  rw [← reassoc_of% core, Iso.hom_inv_id_assoc, hq, op_comp, Functor.map_comp]

/-- **The composition compatibility of the base-change identification, read backwards.** Let
`n : A' ⟶ A` be an arrow of the schemes over `W`, where `A'` is seen over `W` through `k`, and
let `e : W / U ⟶ A / U`, `e' : W' / U ⟶ A' / U` and `m : W' / U ⟶ W / U` be arrows of the slice
over `U` such that `m ≫ e` and `e' ≫ n` have the same underlying morphism of schemes. Then base
change along `g` at `A`, followed by the restriction map along `n`, base change along `k`, the
inverse of `Stacks.Sites.baseChangeCompIso` and the restriction map along `e'`, is the
restriction map along `m ≫ e`. -/
theorem baseChangeCompIso_inv_restriction {A : Over W} {A' : Over W'}
    (n : (Over.map k).obj A' ⟶ A)
    (e : (Over.mk g : Over U) ⟶ (Over.map g).obj A)
    (e' : (Over.mk (k ≫ g) : Over U) ⟶ (Over.map (k ≫ g)).obj A')
    (m : (Over.mk (k ≫ g) : Over U) ⟶ Over.mk g)
    (hm : m.left ≫ e.left = e'.left ≫ n.left) :
    (quasiCoherentPresheafBaseChangeIso 𝓕 (Over.mk g)).hom.app (op A) ≫
        ((quasiCoherentPresheafFunctor W ((Scheme.Modules.pullback g).obj 𝓕)).map n.op ≫
          (quasiCoherentPresheafBaseChangeIso ((Scheme.Modules.pullback g).obj 𝓕)
            (Over.mk k)).hom.app (op A')) ≫
        ((baseChangeCompIso 𝓕 g k A').inv ≫ (quasiCoherentPresheafFunctor U 𝓕).map e'.op) =
      (quasiCoherentPresheafFunctor U 𝓕).map (m ≫ e).op := by
  have hw := over_map_hom_w g k n
  exact baseChangeCompIso_inv_restriction_aux 𝓕 g k n (Over.homMk n.left hw) rfl e' (m ≫ e)
    (Over.OverMorphism.ext hm)

end Tail

end Stacks.Sites

end
