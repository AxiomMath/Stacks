module

public import StacksFrontier.CategoryTheory.Sites.Topos.ToposReplacement
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Replacing a morphism of ringed topoi by a morphism of ringed sites on both sides

Let `(f, f♯) : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed topoi. Stacks 03CR factors it
as a commutative square

```
(Sh(C), O_C)   --(g, g♯)-->   (Sh(C'), O_{C'})
     |                               |
  (f, f♯)                        (h, h♯)
     |                               |
     v                               v
(Sh(D), O_D)   --(e, e♯)-->   (Sh(D'), O_{D'})
```

in which `g` and `e` are the equivalences of topoi induced by special cocontinuous functors
`C ⥤ C'` and `D ⥤ D'`, the two new structure sheaves are the direct images `O_{C'} = g_*O_C` and
`O_{D'} = e_*O_D` with `g♯` and `e♯` the identity, `C'` and `D'` have all finite limits and
subcanonical topologies, prescribed families of sheaves on `C` and on `D` become representable on
`C'` and on `D'`, and `h` comes from a continuous functor `u : D' ⥤ C'` preserving all finite
limits, hence a morphism of sites. It is Stacks 03CJ, the un-ringed statement, with the sheaves of
rings carried along.

## Main results

* `AlgebraicGeometry.RingedToposHom.exists_twoSided_isDenseSubsite_morphismOfSites` (Stacks 03CR):
  the factorization above, with all of its stated properties.
* `AlgebraicGeometry.RingedToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence` (Stacks 03CR,
  the addendum): when `(f, f♯)` is an equivalence of ringed topoi the factorization may be taken
  over a single replacement site `C' = D'`, with the two replacement structure sheaves identified
  and `(h, h♯)` the identity.

## Implementation notes

The square is asserted to commute as a 2-isomorphism `AlgebraicGeometry.RingedToposHom.TwoIso` of
the two composites, which is what Stacks 04IC provides and what "the diagram commutes" means for
ringed topoi: the direct image of a composite of morphisms of topoi is only canonically isomorphic,
not equal, to the composite of the direct images.

The middle morphism `h♯` is pinned, not chosen: it is `f♯` followed by the ring-level incarnation
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso` of the un-ringed square and the
comparison `MorphismOfTopoi.pushforwardRingCompIso` of iterated direct images. The first of these
exists because transporting the ring operations of a sheaf along a finite-product-preserving
functor of sheaves of sets is functorial in that functor, so a natural isomorphism of the two
direct images is automatically an isomorphism of sheaves of commutative rings; both are the given
natural isomorphism on underlying sheaves of sets, which is what makes the 2-isomorphism's
compatibility equation hold.

**What of Stacks 03CR is carried, and what is not.** The source's conclusions are numbered (1) to
(7) in the order they appear, followed by an addendum about an equivalence.

* Conclusions (1) and (2) — `g` and `e` are the equivalences induced by special cocontinuous
  functors `C ⥤ C'`, `D ⥤ D'` — are carried, as the two `Functor.IsDenseSubsite` fields together
  with the two assertions that the direct images are equivalences of categories.
* Conclusions (3) and (4) — `O_{C'} = g_*O_C` and `O_{D'} = e_*O_D`, with `g♯` and `e♯` the obvious
  maps — are carried definitionally: the two replacement ringed topoi are *defined* with those
  structure sheaves and the two structure maps are the identity.
* Conclusion (5) — the sites `C'` and `D'` have final objects and fibre products — is carried for
  both sites, as `HasFiniteLimits C'` and `HasFiniteLimits D'`, together with `J'.Subcanonical` and
  `K'.Subcanonical`.
* Conclusion (6) — `h` comes from a continuous `u : D' ⥤ C'` commuting with all finite limits, to
  which Stacks 00X6 applies — is carried in the strongest available form: `u.IsContinuous`,
  `PreservesFiniteLimits u` and `HasFiniteLimits D'`, plus the two consequences
  `RepresentablyFlat u` (Stacks 00X3) and `u.IsMorphismOfSites` (Stacks 00X6) spelled out, and the
  identification of `h`'s underlying morphism of topoi with the one Stacks 00XC attaches to that
  morphism of sites.
* Conclusion (7) — a prescribed set of sheaves on `C` (resp. `D`) may be assumed representable on
  `C'` (resp. `D'`) — is carried on both sides: the two families are arguments of the statement,
  and each `g_*(F i)` and each `e_*(G j)` is asserted to be a representable sheaf.
* The addendum, that an equivalence `(f, f♯)` can be factored with `C' = D'`, `O_{C'} = O_{D'}` and
  `(h, h♯)` the identity, is carried by
  `AlgebraicGeometry.RingedToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence`, on top of the
  un-ringed addendum `MorphismOfTopoi.exists_oneSided_isDenseSubsite_of_isEquivalence` (Stacks
  03CK). "Equivalence of ringed topoi" is the project's spelling
  `[f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]`, and `C' = D'` is literal: one site,
  one topology, one pair of `HasFiniteLimits` and `Subcanonical` hypotheses, and the two special
  cocontinuous functors `v : C ⥤ C'` and `w : D ⥤ C'` land in it.

  One clause of that addendum is necessarily read up to isomorphism. The two replacement structure
  sheaves are pinned by conclusions (3) and (4) to be the *terms* `g_*O_C` and `e_*O_D`, which are
  canonically isomorphic — by the direct image of `f♯` along `e`, read through the comparison of
  iterated direct images — but not equal, so the two replacement ringed topoi `X'` and `Y'` are not
  the same term and `(h, h♯)` cannot literally be `AlgebraicGeometry.RingedToposHom.id`. What is
  stated instead is the strongest form that type checks and is equivalent to it:
  `h.toToposHom = MorphismOfTopoi.id _` on the nose, and `h♯` an isomorphism — which *is* the
  source's "the structure sheaves agree", since `h♯` is the comparison map of the two of them.
  Keeping conclusions (3) and (4) exact is what forces this; the alternative, defining `O_{D'}` to
  *be* `O_{C'}` so that `h` is the identity on the nose, would move the same isomorphism into `e♯`
  and weaken conclusion (4) instead.

The universes are forced to be those of a Stacks site, as in Stacks 03CJ: `C` and `D` are
`SmallCategory`s on `Type u` and the structure sheaves take values in `CommRingCat.{u}`, so the
ringed topoi are `RingedTopos.{u, u, u}`. See the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Topos/ToposReplacement.lean` for why.

## References

* [Stacks 03CR](https://stacks.math.columbia.edu/tag/03CR)
  (`topologies-lemma-morphism-topoi-comes-from-morphism-sites`)
* [Stacks 03CJ](https://stacks.math.columbia.edu/tag/03CJ),
  [Stacks 03CK](https://stacks.math.columbia.edu/tag/03CK),
  [Stacks 01D3](https://stacks.math.columbia.edu/tag/01D3),
  [Stacks 04IC](https://stacks.math.columbia.edu/tag/04IC),
  [Stacks 00XC](https://stacks.math.columbia.edu/tag/00XC)
-/

@[expose] public section

open CategoryTheory Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local implicit_reducible] MorphismOfTopoi.pushforwardRing
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor

universe u

namespace AlgebraicGeometry.RingedToposHom

/-- A factorization `f_* ≅ g_* ⋙ h_*` of the direct image of a morphism of ringed topoi through an
intermediate site lifts to a factorization of the morphism of *ringed* topoi, once the intermediate
structure sheaf is taken to be `g_*O_C`: the structure map of the middle morphism is `f♯` read
through the given isomorphism, and the square 2-commutes. In particular the middle structure map is
an isomorphism as soon as `f♯` is. -/
private theorem exists_ringedHom_twoIso {X Y : RingedTopos.{u, u, u}} {C : Type u}
    [SmallCategory C] {J : GrothendieckTopology C}
    (g₀ : MorphismOfTopoi X.Topos (Sheaf J (Type u)))
    (h₀ : MorphismOfTopoi (Sheaf J (Type u)) Y.Topos) (f : RingedToposHom X Y)
    (ε : (h₀.comp g₀).pushforward ≅ f.toToposHom.pushforward) :
    let X' : RingedTopos.{u, u, u} :=
      { C := C, J := J, O := g₀.pushforwardRing.obj X.O }
    let g : RingedToposHom X X' := { toToposHom := g₀, fSharp := 𝟙 _ }
    ∃ h : RingedToposHom X' Y, h.toToposHom = h₀ ∧ (IsIso f.fSharp → IsIso h.fSharp) ∧
      Nonempty (TwoIso (A := X) (B := Y)
        (RingedToposHom.comp (X := X) (Y := X') (Z := Y) h g) f) := by
  intro X' g
  let εRing := pullbackCommRingSheafIsoOfNatIso.{u, u, u, u, u, u} Y.J ε X.O
  let cmp := pushforwardCommRingCompIso.{u, u, u, u, u, u, u, u, u} g₀ h₀ X.O
  let h : RingedToposHom X' Y :=
    { toToposHom := h₀, fSharp := f.fSharp ≫ εRing.inv ≫ cmp.inv }
  have hm : h₀.pushforwardRing.map (𝟙 X'.O) ≫ cmp.hom = cmp.hom := by simp
  have hsharp : (RingedToposHom.comp (X := X) (Y := X') (Z := Y) h g).fSharp =
      f.fSharp ≫ εRing.inv := by
    change (f.fSharp ≫ εRing.inv ≫ cmp.inv) ≫ h₀.pushforwardRing.map (𝟙 X'.O) ≫ cmp.hom = _
    simp [hm]
  have hforget : Y.forgetRing.map (RingedToposHom.comp (X := X) (Y := X') (Z := Y) h g).fSharp =
      Y.forgetRing.map f.fSharp ≫ ε.inv.app (X.forgetRing.obj X.O) :=
    (congrArg (Y.forgetRing.map ·) hsharp).trans (Y.forgetRing.map_comp _ _)
  exact ⟨h, rfl, fun _ => inferInstanceAs (IsIso (f.fSharp ≫ εRing.inv ≫ cmp.inv)),
    ⟨{ e := ε, commutes := (ε.app (X.forgetRing.obj X.O)).eq_comp_inv.mp hforget }⟩⟩

/-- **Stacks 03CR.** Let `(f, f♯) : (Sh(C), O_C) → (Sh(D), O_D)` be a morphism of ringed topoi.
Then there are sites `(C', J')` and `(D', K')`, special cocontinuous functors `v : C ⥤ C'` and
`w : D ⥤ D'`, and a functor `u : D' ⥤ C'` such that

1. `v` and `w` exhibit `(C, J)` and `(D, K)` as dense subsites and the morphisms of topoi
   `g : Sh(C) → Sh(C')` and `e : Sh(D) → Sh(D')` they induce are equivalences (Stacks 03A0);
2. the replacement structure sheaves are `O_{C'} = g_*O_C` and `O_{D'} = e_*O_D`, and the structure
   maps `g♯` and `e♯` are the identity;
3. `J'` and `K'` are subcanonical and `C'` and `D'` have all finite limits;
4. `u` is continuous, preserves all finite limits, is representably flat and defines a morphism of
   sites — in other words Stacks 00X6 applies to `u`;
5. each `g_*(F i)` is a representable sheaf on `C'` and each `e_*(G j)` is a representable sheaf on
   `D'`, for prescribed families of sheaves `F` on `C` and `G` on `D`; and
6. there is a morphism of ringed topoi `(h, h♯) : (Sh(C'), O_{C'}) → (Sh(D'), O_{D'})` whose
   underlying morphism of topoi is the one Stacks 00XC attaches to the morphism of sites `u`, and
   for which the square `(h, h♯) ∘ (g, g♯) ≅ (e, e♯) ∘ (f, f♯)` 2-commutes.

The source's addendum, on the case of an equivalence, is
`AlgebraicGeometry.RingedToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence`. -/
@[stacks 03CR "Every morphism of ringed topoi fits into a commutative square whose two vertical
  arrows are the equivalences induced by special cocontinuous functors, with the replacement
  structure sheaves the direct images of the given ones and the two structure maps the identity,
  and whose bottom arrow comes from a continuous functor `u : D' ⥤ C'` preserving all finite
  limits, with both replacement sites having all finite limits and subcanonical topologies and
  with prescribed families of sheaves becoming representable on them. Conclusions (1)-(7); the
  addendum on an equivalence is `exists_oneSided_isDenseSubsite_of_isEquivalence`."]
theorem exists_twoSided_isDenseSubsite_morphismOfSites (X Y : RingedTopos.{u, u, u})
    (f : RingedToposHom X Y) {ι : Type u} (F : ι → Sheaf X.J (Type u)) {κ : Type u}
    (G : κ → Sheaf Y.J (Type u)) :
    ∃ (C' : Type u) (_ : SmallCategory C') (J' : GrothendieckTopology C') (D' : Type u)
      (_ : SmallCategory D') (K' : GrothendieckTopology D') (v : X.C ⥤ C') (w : Y.C ⥤ D')
      (u : D' ⥤ C') (_ : v.IsDenseSubsite X.J J') (_ : w.IsDenseSubsite Y.J K')
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D') (_ : J'.Subcanonical)
      (_ : K'.Subcanonical) (_ : u.IsContinuous K' J')
      (_ : PreservesFiniteLimits u) (_ : RepresentablyFlat u)
      (hu : u.IsMorphismOfSites K' J'),
      let X' : RingedTopos.{u, u, u} :=
        { C := C', J := J',
          O := (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v).pushforwardRing.obj X.O }
      let Y' : RingedTopos.{u, u, u} :=
        { C := D', J := K',
          O := (Functor.IsDenseSubsite.morphismOfTopoi Y.J K' w).pushforwardRing.obj Y.O }
      let g : RingedToposHom X X' :=
        { toToposHom := Functor.IsDenseSubsite.morphismOfTopoi X.J J' v, fSharp := 𝟙 _ }
      let e : RingedToposHom Y Y' :=
        { toToposHom := Functor.IsDenseSubsite.morphismOfTopoi Y.J K' w, fSharp := 𝟙 _ }
      g.toToposHom.pushforward.IsEquivalence ∧ e.toToposHom.pushforward.IsEquivalence ∧
        (∀ i, (g.toToposHom.pushforward.obj (F i)).obj.IsRepresentable) ∧
        (∀ j, (e.toToposHom.pushforward.obj (G j)).obj.IsRepresentable) ∧
        ∃ h : RingedToposHom X' Y',
          h.toToposHom = hu.morphismOfTopoi ∧
            Nonempty (TwoIso (A := X) (B := Y')
              (RingedToposHom.comp (X := X) (Y := X') (Z := Y') h g)
              (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f)) := by
  obtain ⟨C', instC', J', D', instD', K', v, w, u, instv, instw, hflC, hflD, hsubJ, hsubK, hcont,
    hpfl, hflat, hu, hrepF, hrepG, ⟨iso⟩⟩ :=
    f.toToposHom.exists_twoSided_isDenseSubsite_representablyFlat F G
  refine ⟨C', instC', J', D', instD', K', v, w, u, instv, instw, hflC, hflD, hsubJ, hsubK, hcont,
    hpfl, hflat, hu, ?_⟩
  intro X' Y' g e
  refine ⟨Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence X.J J' v,
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence Y.J K' w, hrepF, hrepG, ?_⟩
  obtain ⟨h, hh, -, hsq⟩ := exists_ringedHom_twoIso (X := X) (Y := Y') (C := C') (J := J')
    (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v) hu.morphismOfTopoi
    (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f) iso.symm
  exact ⟨h, hh, hsq⟩

/-- **Stacks 03CR, the addendum.** If `(f, f♯) : (Sh(C), O_C) → (Sh(D), O_D)` is an *equivalence*
of ringed topoi — that is, `f` is an equivalence of topoi and `f♯` is an isomorphism — then the
factorization of Stacks 03CR may be chosen with the two replacement sites equal, the two
replacement structure sheaves identified, and `(h, h♯)` the identity. Concretely there are a single
site `(C', J')` with all finite limits and a subcanonical topology and special cocontinuous
functors `v : C ⥤ C'` and `w : D ⥤ C'` such that, writing `g` and `e` for the equivalences of
ringed topoi they induce as in Stacks 03CR,

1. prescribed families of sheaves `F` on `C` and `G` on `D` become representable on `C'`; and
2. the middle morphism `(h, h♯)` is the identity: its underlying morphism of topoi is
   `MorphismOfTopoi.id`, its structure map `h♯ : e_*O_D ⟶ g_*O_C` is an isomorphism — this is the
   agreement of the two replacement structure sheaves — and the square
   `(h, h♯) ∘ (g, g♯) ≅ (e, e♯) ∘ (f, f♯)` 2-commutes. -/
@[stacks 03CR "the addendum: an equivalence of ringed topoi is factored over a *single*
  replacement site `C' = D'`, with the middle morphism of ringed topoi the identity — the
  identity morphism of topoi together with an isomorphism `e_*O_D ≅ g_*O_C` of the two
  replacement structure sheaves, which is the agreement of the structure sheaves the source
  asserts. See the module's implementation notes for why that isomorphism cannot be an equality."]
theorem exists_oneSided_isDenseSubsite_of_isEquivalence (X Y : RingedTopos.{u, u, u})
    (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    {ι : Type u} (F : ι → Sheaf X.J (Type u)) {κ : Type u} (G : κ → Sheaf Y.J (Type u)) :
    ∃ (C' : Type u) (_ : SmallCategory C') (J' : GrothendieckTopology C') (v : X.C ⥤ C')
      (w : Y.C ⥤ C') (_ : v.IsDenseSubsite X.J J') (_ : w.IsDenseSubsite Y.J J')
      (_ : HasFiniteLimits C') (_ : J'.Subcanonical),
      let X' : RingedTopos.{u, u, u} :=
        { C := C', J := J',
          O := (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v).pushforwardRing.obj X.O }
      let Y' : RingedTopos.{u, u, u} :=
        { C := C', J := J',
          O := (Functor.IsDenseSubsite.morphismOfTopoi Y.J J' w).pushforwardRing.obj Y.O }
      let g : RingedToposHom X X' :=
        { toToposHom := Functor.IsDenseSubsite.morphismOfTopoi X.J J' v, fSharp := 𝟙 _ }
      let e : RingedToposHom Y Y' :=
        { toToposHom := Functor.IsDenseSubsite.morphismOfTopoi Y.J J' w, fSharp := 𝟙 _ }
      g.toToposHom.pushforward.IsEquivalence ∧ e.toToposHom.pushforward.IsEquivalence ∧
        (∀ i, (g.toToposHom.pushforward.obj (F i)).obj.IsRepresentable) ∧
        (∀ j, (e.toToposHom.pushforward.obj (G j)).obj.IsRepresentable) ∧
        ∃ h : RingedToposHom X' Y',
          h.toToposHom = MorphismOfTopoi.id (Sheaf J' (Type u)) ∧ IsIso h.fSharp ∧
            Nonempty (TwoIso (A := X) (B := Y')
              (RingedToposHom.comp (X := X) (Y := X') (Z := Y') h g)
              (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f)) := by
  obtain ⟨C', instC', J', v, w, instv, instw, hflC, hsubJ, hrepF, hrepG, ⟨iso⟩⟩ :=
    f.toToposHom.exists_oneSided_isDenseSubsite_of_isEquivalence F G
  refine ⟨C', instC', J', v, w, instv, instw, hflC, hsubJ, ?_⟩
  intro X' Y' g e
  refine ⟨Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence X.J J' v,
    Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence Y.J J' w, hrepF, hrepG, ?_⟩
  have hef : IsIso (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f).fSharp := by
    have h₁ : (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f).fSharp =
        ((pushforwardCommRingFunctor e.toToposHom).mapIso (asIso f.fSharp) ≪≫
          pushforwardCommRingCompIso f.toToposHom e.toToposHom X.O).hom :=
      Category.id_comp _
    rw [h₁]
    exact Iso.isIso_hom _
  obtain ⟨h, hh, hfs, hsq⟩ := exists_ringedHom_twoIso (X := X) (Y := Y') (C := C') (J := J')
    (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v) (MorphismOfTopoi.id (Sheaf J' (Type u)))
    (RingedToposHom.comp (X := X) (Y := Y) (Z := Y') e f)
    (Functor.rightUnitor _ ≪≫ iso)
  exact ⟨h, hh, hfs hef, hsq⟩

end AlgebraicGeometry.RingedToposHom

end
