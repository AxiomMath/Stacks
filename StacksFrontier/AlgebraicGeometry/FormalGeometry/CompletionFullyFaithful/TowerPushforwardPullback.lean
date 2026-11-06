module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic

/-!
# Condition (4) of Tag 0EK2 read on morphisms into direct images of pullbacks

Let `T` be a tower of schemes `Y_n ⟶ S` (`Stacks.Algebraization.InfinitesimalTower`), for example
the infinitesimal neighbourhoods of a closed subscheme read over an open neighbourhood, and let
`P`, `Q` be modules on `S`. Condition (4) of [Stacks, Tag 0EK2] for the pair `(P, Q)`
(`Stacks.Algebraization.InfinitesimalTower.IsHomsComplete`) is stated with morphisms of pullbacks
`P|_W ⟶ Q|_W` over the opens `W` containing the support and `P|_{Y_n} ⟶ Q|_{Y_n}` on the terms of
the tower. By the adjunction `g^* ⊣ g_*` these are the morphisms `P ⟶ (W ⟶ S)_* Q|_W` and
`P ⟶ (Y_n ⟶ S)_* Q|_{Y_n}`, and restriction along a factorization becomes composition with a
restriction map of direct images. This file records the condition in that form.

## Main definitions

* `Stacks.Algebraization.pullbackHomEquivPushforward` — `Hom(P, g_* M) ≃ Hom(g^* P, M)`.
* `Stacks.Algebraization.pushforwardPullbackRestriction` — the restriction map
  `g_* g^* Q ⟶ g'_* g'^* Q` attached to a factorization `h ≫ g = g'`.

## Main results

* `Stacks.Algebraization.pullbackHomEquivPushforward_comp` — compatibility of the adjunction
  identification with a factorization `h ≫ g = g'`.
* `Stacks.Algebraization.pullbackHomEquivPushforward_pushforwardPullbackRestriction` — composing
  with the restriction map of direct images is restricting the morphism of pullbacks.
* `Stacks.Algebraization.pushforwardPullbackRestriction_comp` — restriction maps compose.
* `Stacks.Algebraization.InfinitesimalTower.exists_hom_pushforward` — a compatible system of
  morphisms `P ⟶ (Y_n ⟶ S)_* Q|_{Y_n}` comes from a morphism `P ⟶ (W ⟶ S)_* Q|_W` on a
  neighbourhood of the support.
* `Stacks.Algebraization.InfinitesimalTower.eq_of_forall_pushforward` — two morphisms on a
  neighbourhood agreeing on every term agree after shrinking the neighbourhood.

## Implementation notes

The compatibility with a factorization is proved after applying the adjunction for the
composite, using `AlgebraicGeometry.pullbackComp_unit` (the unit of the composite adjunction),
naturality of `Scheme.Modules.pushforwardComp` and of the unit, and the triangle identities.
Transitivity of the restriction maps is reduced, through the injectivity of the adjunction
identification, to transitivity of `Stacks.Algebraization.pullbackHomMap`, which is the cocycle
identity `Stacks.AlgebraicGeometry.RelativeCech.pullbackComp_assoc_app` for the comparison
isomorphisms of pullbacks.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Algebraization

/-- **Morphisms into a direct image are morphisms out of the pullback.** For `g : G ⟶ S`, a
module `P` on `S` and a module `M` on `G`, the adjunction `g^* ⊣ g_*` identifies `P ⟶ g_* M`
with `g^* P ⟶ M`. -/
def pullbackHomEquivPushforward {S G : Scheme.{u}} (g : G ⟶ S) (P : S.Modules) (M : G.Modules) :
    (P ⟶ (Scheme.Modules.pushforward g).obj M) ≃ ((Scheme.Modules.pullback g).obj P ⟶ M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv P M).symm

/-- The comparison of direct images along equal morphisms is the identity at the identity
equality. -/
theorem pushforwardCongr_rfl_hom_app {S G : Scheme.{u}} (g : G ⟶ S) (M : G.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : g = g)).hom.app M = 𝟙 _ := by
  ext U x
  simp [Scheme.Modules.pushforwardCongr_hom_app_app]

/-- The unit of `g^* ⊣ g_*` followed by `g_*` of the morphism adjoint to `β` is `β`. -/
private theorem unit_comp_pushforward_map_homEquiv_symm {S G : Scheme.{u}} (g : G ⟶ S)
    {P : S.Modules} {M : G.Modules} (β : P ⟶ (Scheme.Modules.pushforward g).obj M) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P ≫
      (Scheme.Modules.pushforward g).map
        (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv P M).symm β) = β :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- `Stacks.Algebraization.pullbackHomEquivPushforward_comp` at the factorization
`h ≫ g = h ≫ g`, where the comparisons of pullbacks and of direct images are the composition
isomorphisms. -/
theorem pullbackHomEquivPushforward_comp_aux {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (P : S.Modules) {M : G.Modules} {M' : G'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward h).obj M')
    (β : P ⟶ (Scheme.Modules.pushforward g).obj M) :
    pullbackHomEquivPushforward (h ≫ g) P M'
        (β ≫ (Scheme.Modules.pushforward g).map φ ≫
          (Scheme.Modules.pushforwardComp h g).hom.app M') =
      (Scheme.Modules.pullbackComp h g).inv.app P ≫
        (Scheme.Modules.pullback h).map (pullbackHomEquivPushforward g P M β) ≫
        pullbackHomEquivPushforward h M M' φ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _).injective
  simp only [pullbackHomEquivPushforward, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).unit.app P),
    pullbackComp_unit h g P]
  have n1 := (Scheme.Modules.pushforwardComp h g).hom.naturality
    ((Scheme.Modules.pullback h).map
      (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv P M).symm β))
  have n2 := (Scheme.Modules.pushforwardComp h g).hom.naturality
    (((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv M M').symm φ)
  simp only [Functor.comp_map] at n1 n2
  simp only [Category.assoc]
  rw [← reassoc_of% n1, ← n2]
  have n3 := (Scheme.Modules.pullbackPushforwardAdjunction h).unit.naturality
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv P M).symm β)
  simp only [Functor.id_map, Functor.comp_map] at n3
  have e := unit_comp_pushforward_map_homEquiv_symm h φ
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← n3, Category.assoc, e,
    Functor.map_comp, ← Category.assoc, ← Category.assoc]
  have e2 := unit_comp_pushforward_map_homEquiv_symm g β
  rw [← Category.assoc ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P), e2,
    Category.assoc]

/-- **The adjunction identification is compatible with a factorization.** If `h ≫ g = g'`, the
morphism `g'^* P ⟶ M'` attached to `β : P ⟶ g_* M` followed by `g_* φ`, for `φ : M ⟶ h_* M'`,
is the pullback along `h` of the morphism attached to `β`, followed by the morphism attached to
`φ`. -/
theorem pullbackHomEquivPushforward_comp {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (P : S.Modules) {M : G.Modules} {M' : G'.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward h).obj M')
    (β : P ⟶ (Scheme.Modules.pushforward g).obj M) :
    pullbackHomEquivPushforward g' P M'
        (β ≫ (Scheme.Modules.pushforward g).map φ ≫
          (Scheme.Modules.pushforwardComp h g).hom.app M' ≫
          (Scheme.Modules.pushforwardCongr hh).hom.app M') =
      (pullbackObjFactorIso P h hh).inv ≫
        (Scheme.Modules.pullback h).map (pullbackHomEquivPushforward g P M β) ≫
        pullbackHomEquivPushforward h M M' φ := by
  subst hh
  rw [pushforwardCongr_rfl_hom_app, Category.comp_id, pullbackHomEquivPushforward_comp_aux]
  simp [pullbackObjFactorIso, pullbackFactorIso, Scheme.Modules.pullbackCongr]

/-- **Restriction of morphisms of pullbacks is transitive.** For factorizations `g ≫ b = a`,
`f ≫ a = c` and `f ≫ g = k`, restricting along `g` and then along `f` is restricting along
`k`. -/
theorem pullbackHomMap_pullbackHomMap {Z A B C : Scheme.{u}} (G F : Z.Modules) {a : A ⟶ Z}
    {b : B ⟶ Z} {c : C ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a) (f : C ⟶ A) (hf : f ≫ a = c)
    (k : C ⟶ B) (hk : f ≫ g = k)
    (ψ : (Scheme.Modules.pullback b).obj G ⟶ (Scheme.Modules.pullback b).obj F) :
    pullbackHomMap G F f hf (pullbackHomMap G F g hg ψ) =
      pullbackHomMap G F k (by rw [← hk, Category.assoc, hg, hf]) ψ := by
  subst hg hf hk
  have e : ∀ M : Z.Modules, (Scheme.Modules.pullback ((f ≫ g) ≫ b)).obj M =
      (Scheme.Modules.pullback (f ≫ g ≫ b)).obj M := fun M => by rw [Category.assoc]
  have hG := Stacks.AlgebraicGeometry.RelativeCech.pullbackComp_assoc_app f g b G (e G)
  have hF := Stacks.AlgebraicGeometry.RelativeCech.pullbackComp_assoc_app f g b F (e F)
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality ψ
  simp only [Functor.comp_map] at hn
  simp only [pullbackHomMap, pullbackObjFactorIso, pullbackFactorIso, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Scheme.Modules.pullbackCongr, eqToIso.hom,
    eqToIso.inv, eqToHom_app, eqToHom_refl, Category.comp_id, Category.id_comp,
    Functor.map_comp, Category.assoc]
  have hepi : Epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g b).hom.app G) ≫
      (Scheme.Modules.pullbackComp f (g ≫ b)).hom.app G) :=
    @IsIso.epi_of_iso _ _ _ _ _
      ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g b).app G) ≪≫
        (Scheme.Modules.pullbackComp f (g ≫ b)).app G).isIso_hom
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g b).hom.app G) ≫
    (Scheme.Modules.pullbackComp f (g ≫ b)).hom.app G)]
  conv_lhs => rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, hF, reassoc_of% hn]
  rw [hG]
  simp

/-- **The restriction map of direct images of pullbacks.** For a factorization `h ≫ g = g'` and a
module `Q` on `S`, the map `g_* g^* Q ⟶ g'_* g'^* Q`: `g_*` of the unit of `h^* ⊣ h_*` at
`g^* Q`, followed by the identifications `g_* h_* = (h ≫ g)_* = g'_*` and
`h^* g^* Q ≅ g'^* Q`. -/
def pushforwardPullbackRestriction {S G G' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (Q : S.Modules) :
    (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj Q) ⟶
      (Scheme.Modules.pushforward g').obj ((Scheme.Modules.pullback g').obj Q) :=
  (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _) ≫
    (Scheme.Modules.pushforwardComp h g).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hh).hom.app _ ≫
    (Scheme.Modules.pushforward g').map (pullbackObjFactorIso Q h hh).hom

/-- **Composing with the restriction map of direct images is restricting the morphism of
pullbacks.** If `h ≫ g = g'`, the morphism `g'^* P ⟶ g'^* Q` attached to `β : P ⟶ g_* g^* Q`
followed by the restriction map is the restriction along `h` of the morphism
`g^* P ⟶ g^* Q` attached to `β`. -/
theorem pullbackHomEquivPushforward_pushforwardPullbackRestriction {S G G' : Scheme.{u}}
    (g : G ⟶ S) (h : G' ⟶ G) (g' : G' ⟶ S) (hh : h ≫ g = g') (P Q : S.Modules)
    (β : P ⟶ (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj Q)) :
    pullbackHomEquivPushforward g' P _ (β ≫ pushforwardPullbackRestriction g h g' hh Q) =
      pullbackHomMap P Q h hh (pullbackHomEquivPushforward g P _ β) := by
  have hφ : pullbackHomEquivPushforward h _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _ ≫
        (Scheme.Modules.pushforward h).map (pullbackObjFactorIso Q h hh).hom) =
      (pullbackObjFactorIso Q h hh).hom :=
    (Equiv.symm_apply_eq _).2
      ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv_unit _ _ _).symm
  have key := pullbackHomEquivPushforward_comp g h g' hh P
    ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _ ≫
      (Scheme.Modules.pushforward h).map (pullbackObjFactorIso Q h hh).hom) β
  rw [hφ] at key
  refine Eq.trans ?_ key
  congr 2
  subst hh
  rw [pushforwardPullbackRestriction, pushforwardCongr_rfl_hom_app, pushforwardCongr_rfl_hom_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.pushforwardComp h g).hom.naturality
    (pullbackObjFactorIso Q h (rfl : h ≫ g = h ≫ g)).hom
  simp only [Functor.comp_map] at hn
  exact whisker_eq _ hn.symm

/-- **Restriction maps compose.** For factorizations `h ≫ g = g'`, `h' ≫ g' = g''` and
`h' ≫ h = k`, restricting from `g` to `g'` and then to `g''` is restricting from `g` to `g''`
along `k`. -/
theorem pushforwardPullbackRestriction_comp {S G G' G'' : Scheme.{u}} (g : G ⟶ S) (h : G' ⟶ G)
    (g' : G' ⟶ S) (hh : h ≫ g = g') (h' : G'' ⟶ G') (g'' : G'' ⟶ S) (hh' : h' ≫ g' = g'')
    (k : G'' ⟶ G) (hk : h' ≫ h = k) (Q : S.Modules) :
    pushforwardPullbackRestriction g h g' hh Q ≫ pushforwardPullbackRestriction g' h' g'' hh' Q =
      pushforwardPullbackRestriction g k g''
        (show k ≫ g = g'' by rw [← hk, Category.assoc, hh, hh']) Q := by
  apply (pullbackHomEquivPushforward g'' _ _).injective
  have e2 := pullbackHomEquivPushforward_pushforwardPullbackRestriction g h g' hh _ Q (𝟙 _)
  have e3 := pullbackHomEquivPushforward_pushforwardPullbackRestriction g k g''
    (show k ≫ g = g'' by rw [← hk, Category.assoc, hh, hh']) _ Q (𝟙 _)
  rw [Category.id_comp] at e2 e3
  rw [pullbackHomEquivPushforward_pushforwardPullbackRestriction, e2, e3,
    pullbackHomMap_pullbackHomMap _ _ h hh h' hh' k hk]

namespace InfinitesimalTower

/-- **A compatible system of morphisms into the direct images on the terms of a tower comes from
a neighbourhood of the support.** If condition (4) of [Stacks, Tag 0EK2] holds for the pair
`(P, Q)`, every compatible system of morphisms `P ⟶ (Y_n ⟶ S)_* Q|_{Y_n}` comes from a morphism
`P ⟶ (W ⟶ S)_* Q|_W` for some open `W` containing the support of the tower. -/
theorem exists_hom_pushforward {S : Scheme.{u}} (T : InfinitesimalTower S)
    (P Q : S.Modules) (hPQ : T.IsHomsComplete P Q)
    (α : ∀ n : ℕ, P ⟶ (Scheme.Modules.pushforward (T.obj n).hom).obj
      ((Scheme.Modules.pullback (T.obj n).hom).obj Q))
    (hα : ∀ (n m : ℕ) (h : n ≤ m), α m ≫ pushforwardPullbackRestriction (T.obj m).hom
      (T.trans n m h).left (T.obj n).hom (Over.w (T.trans n m h)) Q = α n) :
    ∃ (W : S.Opens) (hW : T.support ⊆ W)
      (β : P ⟶ (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pullback W.ι).obj Q)),
      ∀ n : ℕ, β ≫ pushforwardPullbackRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
        (T.homToOpen_ι hW n) Q = α n := by
  obtain ⟨W, hW, φ, hφ⟩ := hPQ.exists_hom
    (fun n => pullbackHomEquivPushforward (T.obj n).hom P _ (α n)) (fun n m h =>
      (pullbackHomEquivPushforward_pushforwardPullbackRestriction (T.obj m).hom
        (T.trans n m h).left (T.obj n).hom (Over.w (T.trans n m h)) P Q (α m)).symm.trans
        (congrArg (pullbackHomEquivPushforward (T.obj n).hom P _) (hα n m h)))
  refine ⟨W, hW, (pullbackHomEquivPushforward W.ι P _).symm φ, fun n => ?_⟩
  apply (pullbackHomEquivPushforward (T.obj n).hom P _).injective
  refine (pullbackHomEquivPushforward_pushforwardPullbackRestriction W.ι (T.homToOpen hW n)
    (T.obj n).hom (T.homToOpen_ι hW n) P Q _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact hφ n

/-- **Two morphisms into the direct image on a neighbourhood that agree on every term of a tower
agree on a smaller neighbourhood**, granted condition (4) of [Stacks, Tag 0EK2] for the pair
`(P, Q)`. -/
theorem eq_of_forall_pushforward {S : Scheme.{u}} (T : InfinitesimalTower S)
    (P Q : S.Modules) (hPQ : T.IsHomsComplete P Q) (W : S.Opens) (hW : T.support ⊆ W)
    (a b : P ⟶ (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pullback W.ι).obj Q))
    (hab : ∀ n : ℕ,
      a ≫ pushforwardPullbackRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
          (T.homToOpen_ι hW n) Q =
        b ≫ pushforwardPullbackRestriction W.ι (T.homToOpen hW n) (T.obj n).hom
          (T.homToOpen_ι hW n) Q) :
    ∃ (W' : S.Opens) (_ : T.support ⊆ W') (h : W' ≤ W),
      a ≫ pushforwardPullbackRestriction W.ι (S.homOfLE h) W'.ι (S.homOfLE_ι h) Q =
        b ≫ pushforwardPullbackRestriction W.ι (S.homOfLE h) W'.ι (S.homOfLE_ι h) Q := by
  obtain ⟨W', hW', h₁, _, he⟩ := hPQ.eq_of_homAt_eq W W hW hW
    (pullbackHomEquivPushforward W.ι P _ a) (pullbackHomEquivPushforward W.ι P _ b)
    (fun n =>
      (pullbackHomEquivPushforward_pushforwardPullbackRestriction W.ι (T.homToOpen hW n)
        (T.obj n).hom (T.homToOpen_ι hW n) P Q a).symm.trans
      ((congrArg (pullbackHomEquivPushforward (T.obj n).hom P _) (hab n)).trans
      (pullbackHomEquivPushforward_pushforwardPullbackRestriction W.ι (T.homToOpen hW n)
        (T.obj n).hom (T.homToOpen_ι hW n) P Q b)))
  refine ⟨W', hW', h₁, ?_⟩
  apply (pullbackHomEquivPushforward W'.ι P _).injective
  exact (pullbackHomEquivPushforward_pushforwardPullbackRestriction W.ι (S.homOfLE h₁) W'.ι
    (S.homOfLE_ι h₁) P Q a).trans (he.trans
      (pullbackHomEquivPushforward_pushforwardPullbackRestriction W.ι (S.homOfLE h₁) W'.ι
        (S.homOfLE_ι h₁) P Q b).symm)

end InfinitesimalTower

end Stacks.Algebraization

end
