module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentInto
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentPullback

/-!
# Inverse images of descended modules along a morphism of presentations

Let `h : X'' ⟶ X` be a morphism of algebraic spaces, `X = U/R` and `X'' = U''/R''` presentations,
and `yU : U'' ⟶ U`, `yR : R'' ⟶ R` morphisms of the presenting schemes compatible with the
projections and with `h` on the atlases.  If a quasi-coherent `𝒪_X`-module `𝒯` is identified on
the atlas with the module `M^a` attached to a quasi-coherent module `M` on the scheme of `U`,
compatibly with a scheme transition `τ` of `M` (for instance `𝒯 = D(M)`, descended by
Stacks 03M3), and `Θ : yU^*M ≅ M''` carries the pulled-back transition of `τ` to a transition `τ''`
of a module `M''` on the scheme of `U''`, then the inverse image `h^*𝒯` is the descended module
`D(M'')`.  This is the shape, in each degree, of the isomorphism `θ` of Stacks 085C: the inverse
image of a twist of a relative Proj along a base change is the twist of the base-changed relative
Proj.

## Main definitions

* `AlgebraicGeometry.Space.pairTransition`: the transition morphism `α` of a module on `U`, pulled
  back along `U'' ⟶ U` and read on `R''` through a morphism `R'' ⟶ R` compatible with the
  projections.
* `AlgebraicGeometry.Space.pullbackSquareHom`, `AlgebraicGeometry.Space.pullbackSquareIso`: the
  identification `c''^*(h^*𝒯) ≅ Y^*(c^*𝒯)` along a commutative square `c'' ≫ h = Y ≫ c`.
* `AlgebraicGeometry.Space.schemePairTransition`: the pulled-back transition of a scheme
  transition.
* `AlgebraicGeometry.Space.presentationDescendedIso`: the isomorphism `𝒴 ≅ D(M)` attached to an
  identification on the atlas compatible with the transitions (Stacks 03M3).
* `AlgebraicGeometry.Space.presentationPullbackChartIso`: the identification
  `c''^*(h^*𝒯) ≅ M''^a` on the atlas of `X''`.

## Main results

* `AlgebraicGeometry.Space.pairTransition_naturality`: the pulled-back transition is natural in
  the module.
* `AlgebraicGeometry.Space.transitionCommutes_pullbackSquareHom`: the identification along a
  square carries the canonical transition of `c''^*(h^*𝒯)` to the pulled-back canonical
  transition of `c^*𝒯` (the coherence of Stacks 03LU).
* `AlgebraicGeometry.Space.transitionCommutes_pairTransition_representedSchemeTransition`: the
  pulled-back transition of `τ^a` is the transition attached to the pulled-back scheme
  transition.
* `AlgebraicGeometry.Space.transitionCommutes_presentationPullbackChartHom`: **the identification
  on the atlas carries the canonical transition of `c''^*(h^*𝒯)` to `τ''^a`**, so that
  `AlgebraicGeometry.Space.presentationDescendedIso` gives `h^*𝒯 ≅ D(M'')`.
* `AlgebraicGeometry.Space.presentationDescendedIso_spec`: the inverse image along the atlas of
  the descended isomorphism is the identification on the atlas.

## Implementation notes

All comparisons of iterated inverse images are written through
`AlgebraicGeometry.Space.modulePullbackCompHom` and
`AlgebraicGeometry.Space.modulePullbackCompInv`, so that every morphism is typed with the iterated
inverse images spelled out: an equation whose two sides spell the same module once as `f^*(g^*ℳ)`
and once as `(g^* ⋙ f^*) ℳ`, inverse-imaged once more, exhausts the kernel's budget.  The
associativity coherence is used only through
`AlgebraicGeometry.Space.modulePullbackCompHom_assoc_transport`, whose two sides end with a
transport to a common composite, so that no rewrite changes the type of a term.  Morphisms of
represented spaces are composed in `AlgebraicGeometry.Space.AlgebraicSpaces`
(`AlgebraicGeometry.Space.algebraicSpacesComp_representedSpaceMap`), and inverse images along the
represented chart morphism of a presentation are typed over the object spaces of its groupoid:
two spellings of the same object met in one equation exhaust the elaborator's budget.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transition morphisms read through other transitions -/

section Abstract

variable {C D : Type*} [Category C] [Category D] (Pt Ps : C ⥤ D)

/-- A compatibility `α ≫ s^*f = t^*f ≫ β` along an isomorphism `f` gives the compatibility
along `f⁻¹`. -/
theorem transitionSquare_symm {A A' : C} (α : Pt.obj A ⟶ Ps.obj A) (β : Pt.obj A' ⟶ Ps.obj A')
    (f : A ≅ A') (hf : α ≫ Ps.map f.hom = Pt.map f.hom ≫ β) :
    β ≫ Ps.map f.inv = Pt.map f.inv ≫ α := by
  rw [← cancel_epi (Pt.map f.hom), ← reassoc_of% hf, ← Ps.map_comp, f.hom_inv_id,
    ← Pt.map_comp_assoc, f.hom_inv_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- Compatibilities along `f` and `g` compose to the compatibility along `f ≫ g`. -/
theorem transitionSquare_comp {A A' A'' : C} (α : Pt.obj A ⟶ Ps.obj A)
    (β : Pt.obj A' ⟶ Ps.obj A') (γ : Pt.obj A'' ⟶ Ps.obj A'') (f : A ⟶ A') (g : A' ⟶ A'')
    (hf : α ≫ Ps.map f = Pt.map f ≫ β) (hg : β ≫ Ps.map g = Pt.map g ≫ γ) :
    α ≫ Ps.map (f ≫ g) = Pt.map (f ≫ g) ≫ γ := by
  rw [Ps.map_comp, reassoc_of% hf, hg, Pt.map_comp_assoc]

/-- **A compatibility from readings**: if two transitions `α`, `β` are read to a common object `Q`
through `ρa, ρb` and `ρa', ρb'`, and the inverse images of `f` carry the readings of `β` to
those of `α`, then `α ≫ s^*f = t^*f ≫ β`. -/
theorem transitionSquare_of_readings {A A' : C} {Q : D} (α : Pt.obj A ⟶ Ps.obj A)
    (β : Pt.obj A' ⟶ Ps.obj A') (f : A ⟶ A') (ρa : Pt.obj A ⟶ Q) (ρb : Ps.obj A ⟶ Q)
    (ρa' : Pt.obj A' ⟶ Q) (ρb' : Ps.obj A' ⟶ Q) (σ : Q ⟶ Ps.obj A') (hσ : ρb' ≫ σ = 𝟙 _)
    (hα : α ≫ ρb = ρa) (hβ : β ≫ ρb' = ρa') (ha : Pt.map f ≫ ρa' = ρa)
    (hb : Ps.map f ≫ ρb' = ρb) :
    α ≫ Ps.map f = Pt.map f ≫ β := by
  have key : (α ≫ Ps.map f) ≫ ρb' = (Pt.map f ≫ β) ≫ ρb' := by
    rw [Category.assoc, hb, hα, Category.assoc, hβ, ha]
  have := congrArg (· ≫ σ) key
  simpa only [Category.assoc, hσ, Category.comp_id] using this

end Abstract

/-! ### The comparisons of Stacks 03LU, read to a common composite -/

section Comparison

variable (B S hS)

/-- **The associativity coherence of Stacks 03LU, read on the inverse image along a common
composite `Q`**: both sides end at `Q^*ℳ`, so rewriting with it never changes a type. -/
@[reassoc]
theorem modulePullbackCompHom_assoc_transport {V W W' X : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (g : W ⟶ W') (k : W' ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) {Q : V ⟶ X}
    (e : (f ≫ g) ≫ k = Q) (e' : f ≫ g ≫ k = Q) :
    modulePullbackCompHom B S hS f g ((modulePullback B S hS k).obj M) ≫
        modulePullbackCompHom B S hS (f ≫ g) k M ≫ pullbackTransport M e =
      (modulePullback B S hS f).map (modulePullbackCompHom B S hS g k M) ≫
        modulePullbackCompHom B S hS f (g ≫ k) M ≫ pullbackTransport M e' := by
  subst e
  have h0 : pullbackTransport M (rfl : (f ≫ g) ≫ k = (f ≫ g) ≫ k) = 𝟙 _ := rfl
  have h1 : pullbackTransport M e' = pullbackTransport M (rfl : (f ≫ g) ≫ k = (f ≫ g) ≫ k) :=
    rfl
  rewrite [h1, h0, Category.comp_id]
  exact ((modulePullbackCompIsoAssoc (B := B) (S := S) (hS := hS)).hom_app f g k M).symm.trans
    (Category.comp_id _).symm

/-- The comparison along `y ≫ g` after the inverse image along `y` of a transport along `f = g`
is the comparison along `y ≫ f` followed by a transport. -/
@[reassoc]
theorem modulePullback_map_pullbackTransport_comp_compHom {V W X : AlgebraicSpaces B S hS}
    (y : V ⟶ W) {f g : W ⟶ X} (e : f = g) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS y).map (pullbackTransport M e) ≫ modulePullbackCompHom B S hS y g M =
      modulePullbackCompHom B S hS y f M ≫ pullbackTransport M (congrArg (y ≫ ·) e) := by
  subst e
  simp [pullbackTransport]

/-- A transport along `a = b` of an inverse image along `π`, followed by the comparison along
`b ≫ π`, is the comparison along `a ≫ π` followed by a transport. -/
@[reassoc]
theorem pullbackTransport_comp_compHom {V W X : AlgebraicSpaces B S hS} (π : W ⟶ X)
    {a b : V ⟶ W} (e : a = b) (M : Modules.{u, u} B S hS X.1 X.2) :
    pullbackTransport ((modulePullback B S hS π).obj M) e ≫ modulePullbackCompHom B S hS b π M =
      modulePullbackCompHom B S hS a π M ≫ pullbackTransport M (congrArg (· ≫ π) e) := by
  subst e
  simp [pullbackTransport]

/-- Unflattening, followed by the comparison along the source, is the comparison along the
target followed by the unflattened morphism. -/
@[reassoc]
theorem modulePullbackUnflatten_comp_compHom {V W X : AlgebraicSpaces B S hS} (t s : V ⟶ W)
    (φ : W ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2)
    (x : (modulePullback B S hS (t ≫ φ)).obj M ⟶ (modulePullback B S hS (s ≫ φ)).obj M) :
    modulePullbackUnflatten φ x ≫ modulePullbackCompHom B S hS s φ M =
      modulePullbackCompHom B S hS t φ M ≫ x := by
  rw [modulePullbackUnflatten_eq_compHom, Category.assoc, Category.assoc,
    modulePullbackCompInv_comp_compHom, Category.comp_id]

/-- Reindexing, through `AlgebraicGeometry.Space.modulePullbackCompHom` and
`AlgebraicGeometry.Space.modulePullbackCompInv`. -/
theorem modulePullbackReindex_eq_compHom {V W X : AlgebraicSpaces B S hS} (f : V ⟶ W)
    {a b : W ⟶ X} {M : Modules.{u, u} B S hS X.1 X.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    modulePullbackReindex f α =
      modulePullbackCompInv B S hS f a M ≫ (modulePullback B S hS f).map α ≫
        modulePullbackCompHom B S hS f b M :=
  rfl

/-- Three transports in a row are one transport. -/
@[reassoc]
theorem pullbackTransport_comp_comp_eq {T X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {a b c d : T ⟶ X} (e₁ : a = b) (e₂ : b = c) (e₃ : c = d)
    (e : a = d) :
    pullbackTransport F e₁ ≫ pullbackTransport F e₂ ≫ pullbackTransport F e₃ =
      pullbackTransport F e := by
  subst e₁ e₂ e₃
  rfl

/-- Two pairs of transports with the same endpoints agree. -/
@[reassoc]
theorem pullbackTransport_comp_eq_comp {T X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {a b b' c : T ⟶ X} (e₁ : a = b) (e₂ : b = c)
    (e₃ : a = b') (e₄ : b' = c) :
    pullbackTransport F e₁ ≫ pullbackTransport F e₂ =
      pullbackTransport F e₃ ≫ pullbackTransport F e₄ := by
  subst e₁ e₂ e₃
  rfl

/-- Flattening, through `AlgebraicGeometry.Space.modulePullbackCompHom` and
`AlgebraicGeometry.Space.modulePullbackCompInv`. -/
theorem modulePullbackFlatten_eq_compHom {V W X : AlgebraicSpaces B S hS} (f : W ⟶ X)
    {a b : V ⟶ W} {M : Modules.{u, u} B S hS X.1 X.2}
    (α : (modulePullback B S hS a).obj ((modulePullback B S hS f).obj M) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS f).obj M)) :
    modulePullbackFlatten f α =
      modulePullbackCompInv B S hS a f M ≫ α ≫ modulePullbackCompHom B S hS b f M :=
  rfl

/-- **The canonical transition morphism of an inverse image, read to a common composite**: the
unflattened transport of `π^*ℳ` along `t ≫ φ = s ≫ φ`, followed by the comparisons along `s`
and `s ≫ φ`, is the comparisons along `t` and `t ≫ φ`, for `Q = (t ≫ φ) ≫ π = (s ≫ φ) ≫ π`. -/
theorem modulePullbackUnflatten_pullbackTransport_comp_compHom {V W P X : AlgebraicSpaces B S hS}
    (t s : V ⟶ W) (φ : W ⟶ P) (hφ : t ≫ φ = s ≫ φ) (π : P ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) {Q : V ⟶ X} (ht : (t ≫ φ) ≫ π = Q)
    (hs : (s ≫ φ) ≫ π = Q) :
    modulePullbackUnflatten φ (pullbackTransport ((modulePullback B S hS π).obj M) hφ) ≫
        modulePullbackCompHom B S hS s φ ((modulePullback B S hS π).obj M) ≫
          modulePullbackCompHom B S hS (s ≫ φ) π M ≫ pullbackTransport M hs =
      modulePullbackCompHom B S hS t φ ((modulePullback B S hS π).obj M) ≫
        modulePullbackCompHom B S hS (t ≫ φ) π M ≫ pullbackTransport M ht := by
  rewrite [modulePullbackUnflatten_comp_compHom_assoc B S hS t s φ _ _,
    pullbackTransport_comp_compHom_assoc B S hS π hφ M,
    pullbackTransport_comp M (congrArg (· ≫ π) hφ) hs ht]
  rfl

end Comparison

/-! ### The pulled-back transition morphism -/

section Pair

variable {U'' R'' U R : AlgebraicSpaces B S hS} {a b : R'' ⟶ U''} {p q : R ⟶ U}
  (Y : U'' ⟶ U) (Z : R'' ⟶ R) (hta : a ≫ Y = Z ≫ p) (hsb : Z ≫ q = b ≫ Y)

/-- The reindexing of a transition morphism `α : p^*ℱ ⟶ q^*ℱ` along `Z : R'' ⟶ R`, read between
the two squares `a ≫ Y = Z ≫ p` and `Z ≫ q = b ≫ Y`. -/
def pairReindexTransport (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    (modulePullback B S hS (a ≫ Y)).obj F ⟶ (modulePullback B S hS (b ≫ Y)).obj F :=
  comp₃ (pullbackTransport F hta) (modulePullbackReindex Z α) (pullbackTransport F hsb)

/-- `pairReindexTransport` is the threefold composite of the transports along `hta` and `hsb`
with the reindexing of `α` along `Z`. -/
theorem pairReindexTransport_eq (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    pairReindexTransport Y Z hta hsb F α =
      comp₃ (pullbackTransport F hta) (modulePullbackReindex Z α) (pullbackTransport F hsb) :=
  rfl

/-- `pairReindexTransport` is the composite of the transport along `hta`, the reindexing of `α`
along `Z`, and the transport along `hsb`. -/
theorem pairReindexTransport_eq_comp (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    pairReindexTransport Y Z hta hsb F α =
      pullbackTransport F hta ≫ modulePullbackReindex Z α ≫ pullbackTransport F hsb :=
  (pairReindexTransport_eq Y Z hta hsb F α).trans (comp₃_eq _ _ _)

/-- **The transition morphism `α : p^*ℱ ⟶ q^*ℱ` pulled back along a pair `(Y, Z)`** of morphisms
`Y : U'' ⟶ U`, `Z : R'' ⟶ R` compatible with the two pairs of projections: the reindexing of `α`
along `Z`, read between the two squares and unflattened along `Y`, a morphism
`a^*(Y^*ℱ) ⟶ b^*(Y^*ℱ)`.  For a morphism of groupoids this is the transition morphism of the
inverse image (`AlgebraicGeometry.Space.groupoidModulePullbackTransition`). -/
def pairTransition (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    (modulePullback B S hS a).obj ((modulePullback B S hS Y).obj F) ⟶
      (modulePullback B S hS b).obj ((modulePullback B S hS Y).obj F) :=
  modulePullbackUnflatten Y (a := a) (b := b) (M := F) (pairReindexTransport Y Z hta hsb F α)

/-- `pairTransition` is the unflattening along `Y` of `pairReindexTransport`. -/
theorem pairTransition_eq (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    pairTransition Y Z hta hsb F α =
      modulePullbackUnflatten Y (a := a) (b := b) (M := F) (pairReindexTransport Y Z hta hsb F α) :=
  rfl

/-- **The pulled-back transition morphism is natural in the module.** -/
theorem pairTransition_naturality {F N : Modules.{u, u} B S hS U.1 U.2}
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F)
    (β : (modulePullback B S hS p).obj N ⟶ (modulePullback B S hS q).obj N) (φ : F ⟶ N)
    (hφ : α ≫ (modulePullback B S hS q).map φ = (modulePullback B S hS p).map φ ≫ β) :
    pairTransition Y Z hta hsb F α ≫
        (modulePullback B S hS b).map ((modulePullback B S hS Y).map φ) =
      (modulePullback B S hS a).map ((modulePullback B S hS Y).map φ) ≫
        pairTransition Y Z hta hsb N β :=
  (comp₂_congr (pairTransition_eq Y Z hta hsb F α) rfl).trans
    ((modulePullbackUnflatten_naturality Y φ
          (pairReindexTransport Y Z hta hsb F α) (pairReindexTransport Y Z hta hsb N β)
          (((comp₂_congr (pairReindexTransport_eq_comp Y Z hta hsb F α) rfl).trans
                (transportReindexTransport_naturality Z hta hsb α β φ hφ)).trans
            (comp₂_congr rfl (pairReindexTransport_eq_comp Y Z hta hsb N β).symm))).trans
      (comp₂_congr rfl (pairTransition_eq Y Z hta hsb N β).symm))

/-- **The pulled-back transition, read to a common composite**: followed by the comparisons
along `b` and `b ≫ Y`, it is the comparison along `a` followed by the reindexing of `α` read
between the two squares. -/
@[reassoc]
theorem pairTransition_comp_compHom (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F) :
    pairTransition Y Z hta hsb F α ≫ modulePullbackCompHom B S hS b Y F =
      modulePullbackCompHom B S hS a Y F ≫ pullbackTransport F hta ≫
        modulePullbackReindex Z α ≫ pullbackTransport F hsb := by
  rewrite [pairTransition_eq Y Z hta hsb F α,
    modulePullbackUnflatten_comp_compHom B S hS a b Y F _,
    pairReindexTransport_eq_comp Y Z hta hsb F α]
  rfl

/-- **The pulled-back transition of a transition read through identifications**: if the
reindexing of `α` along `Z` is read, through transports to `zT = Z ≫ p` and `zS = Z ≫ q` and
morphisms `c₃`, as a morphism `As`, and the readings at `zT`, `zS` and at `kT = a ≫ Y`,
`kS = b ≫ Y` are compatible along `kT = zT` and `zS = kS`, then the pulled-back transition,
read at `kS`, is the reading at `kT` followed by `Aet ≫ As ≫ Aes`. -/
theorem pairTransition_comp_of_readings (F : Modules.{u, u} B S hS U.1 U.2)
    (α : (modulePullback B S hS p).obj F ⟶ (modulePullback B S hS q).obj F)
    {kT kS zT zS : R'' ⟶ U} (eT : a ≫ Y = kT) (eS : b ≫ Y = kS) (fT : Z ≫ p = zT)
    (fS : Z ≫ q = zS) (gT : kT = zT) (gS : zS = kS)
    {NkT NkS NzT NzS : Modules.{u, u} B S hS R''.1 R''.2}
    (c₃kT : (modulePullback B S hS kT).obj F ⟶ NkT) (c₃kS : (modulePullback B S hS kS).obj F ⟶ NkS)
    (c₃zT : (modulePullback B S hS zT).obj F ⟶ NzT) (c₃zS : (modulePullback B S hS zS).obj F ⟶ NzS)
    (c₃zSinv : NzS ⟶ (modulePullback B S hS zS).obj F) (As : NzT ⟶ NzS) (Aes : NzS ⟶ NkS)
    (Aet : NkT ⟶ NzT) (Aω : NkT ⟶ NkS)
    (hR : modulePullbackReindex Z α =
      pullbackTransport F fT ≫ c₃zT ≫ As ≫ c₃zSinv ≫ pullbackTransport F fS.symm)
    (hcS : pullbackTransport F gS ≫ c₃kS = c₃zS ≫ Aes) (hinv : c₃zSinv ≫ c₃zS = 𝟙 NzS)
    (hcT : pullbackTransport F gT ≫ c₃zT = c₃kT ≫ Aet) (hω : Aω = Aet ≫ As ≫ Aes) :
    pairTransition Y Z hta hsb F α ≫ modulePullbackCompHom B S hS b Y F ≫
        pullbackTransport F eS ≫ c₃kS =
      modulePullbackCompHom B S hS a Y F ≫ pullbackTransport F eT ≫ c₃kT ≫ Aω := by
  rw [pairTransition_comp_compHom_assoc Y Z hta hsb F α, hR]
  simp only [Category.assoc]
  rw [pullbackTransport_comp_comp_eq_assoc B S hS F fS.symm hsb eS gS, hcS,
    reassoc_of% hinv, pullbackTransport_comp_eq_comp_assoc B S hS F hta fT eT gT,
    reassoc_of% hcT, hω]


end Pair

/-! ### The identification along a square -/

section Square

variable {V U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
  (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c) (T : Modules.{u, u} B S hS X.1 X.2)

/-- **The identification `c''^*(h^*𝒯) ≅ Y^*(c^*𝒯)` along a commutative square
`c'' ≫ h = Y ≫ c`**: the comparisons of Stacks 03LU and the transport along the square. -/
def pullbackSquareHom :
    (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ⟶
      (modulePullback B S hS Y).obj ((modulePullback B S hS c).obj T) :=
  comp₃ (modulePullbackCompHom B S hS c'' h T) (pullbackTransport T hY)
    (modulePullbackCompInv B S hS Y c T)

/-- `pullbackSquareHom` is the threefold composite of `modulePullbackCompHom` along `(c'', h)`,
the transport along `hY`, and `modulePullbackCompInv` along `(Y, c)`. -/
theorem pullbackSquareHom_eq :
    pullbackSquareHom c'' c h Y hY T =
      comp₃ (modulePullbackCompHom B S hS c'' h T) (pullbackTransport T hY)
        (modulePullbackCompInv B S hS Y c T) :=
  rfl

/-- `pullbackSquareHom` is the composite of `modulePullbackCompHom` along `(c'', h)`, the
transport along `hY`, and `modulePullbackCompInv` along `(Y, c)`. -/
theorem pullbackSquareHom_eq_comp :
    pullbackSquareHom c'' c h Y hY T =
      modulePullbackCompHom B S hS c'' h T ≫ pullbackTransport T hY ≫
        modulePullbackCompInv B S hS Y c T :=
  (pullbackSquareHom_eq c'' c h Y hY T).trans (comp₃_eq _ _ _)

/-- The inverse identification `Y^*(c^*𝒯) ⟶ c''^*(h^*𝒯)`. -/
def pullbackSquareInv :
    (modulePullback B S hS Y).obj ((modulePullback B S hS c).obj T) ⟶
      (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) :=
  comp₃ (modulePullbackCompHom B S hS Y c T) (pullbackTransport T hY.symm)
    (modulePullbackCompInv B S hS c'' h T)

/-- `pullbackSquareInv` is the threefold composite of `modulePullbackCompHom` along `(Y, c)`,
the transport along `hY.symm`, and `modulePullbackCompInv` along `(c'', h)`. -/
theorem pullbackSquareInv_eq :
    pullbackSquareInv c'' c h Y hY T =
      comp₃ (modulePullbackCompHom B S hS Y c T) (pullbackTransport T hY.symm)
        (modulePullbackCompInv B S hS c'' h T) :=
  rfl

/-- `pullbackSquareInv` is the composite of `modulePullbackCompHom` along `(Y, c)`, the
transport along `hY.symm`, and `modulePullbackCompInv` along `(c'', h)`. -/
theorem pullbackSquareInv_eq_comp :
    pullbackSquareInv c'' c h Y hY T =
      modulePullbackCompHom B S hS Y c T ≫ pullbackTransport T hY.symm ≫
        modulePullbackCompInv B S hS c'' h T :=
  (pullbackSquareInv_eq c'' c h Y hY T).trans (comp₃_eq _ _ _)

/-- The identification along a square, as an isomorphism. -/
def pullbackSquareIso :
    (modulePullback B S hS c'').obj ((modulePullback B S hS h).obj T) ≅
      (modulePullback B S hS Y).obj ((modulePullback B S hS c).obj T) where
  hom := pullbackSquareHom c'' c h Y hY T
  inv := pullbackSquareInv c'' c h Y hY T
  hom_inv_id := by
    rewrite [pullbackSquareHom_eq_comp c'' c h Y hY T, pullbackSquareInv_eq_comp c'' c h Y hY T,
      Category.assoc, Category.assoc,
      reassoc_of% (modulePullbackCompInv_comp_compHom B S hS Y c T),
      reassoc_of% (pullbackTransport_comp T hY hY.symm rfl)]
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
      (modulePullbackCompHom_comp_compInv B S hS c'' h T)
  inv_hom_id := by
    rewrite [pullbackSquareHom_eq_comp c'' c h Y hY T, pullbackSquareInv_eq_comp c'' c h Y hY T,
      Category.assoc, Category.assoc,
      reassoc_of% (modulePullbackCompInv_comp_compHom B S hS c'' h T),
      reassoc_of% (pullbackTransport_comp T hY.symm hY rfl)]
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans
      (modulePullbackCompHom_comp_compInv B S hS Y c T)

/-- The forward morphism of `pullbackSquareIso` is `pullbackSquareHom`. -/
theorem pullbackSquareIso_hom : (pullbackSquareIso c'' c h Y hY T).hom =
    pullbackSquareHom c'' c h Y hY T :=
  rfl

/-- The inverse image along `y` of the identification along a square. -/
theorem modulePullback_map_pullbackSquareHom (y : V ⟶ U'') :
    (modulePullback B S hS y).map (pullbackSquareHom c'' c h Y hY T) =
      (modulePullback B S hS y).map (modulePullbackCompHom B S hS c'' h T) ≫
        (modulePullback B S hS y).map (pullbackTransport T hY) ≫
          (modulePullback B S hS y).map (modulePullbackCompInv B S hS Y c T) :=
  (congrArg (modulePullback B S hS y).map (pullbackSquareHom_eq_comp c'' c h Y hY T)).trans
    (((modulePullback B S hS y).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((modulePullback B S hS y).map_comp _ _)))

/-- **The identification along a square, pulled back along `y` and read to a common composite,
is the comparison**: both read on the inverse image along `Q = (y ≫ c'') ≫ h = (y ≫ Y) ≫ c`. -/
theorem modulePullback_map_pullbackSquareHom_comp_compHom (y : V ⟶ U'') {Q : V ⟶ X}
    (e3 : (y ≫ c'') ≫ h = Q) (e4 : (y ≫ Y) ≫ c = Q) :
    (modulePullback B S hS y).map (pullbackSquareHom c'' c h Y hY T) ≫
        modulePullbackCompHom B S hS y Y ((modulePullback B S hS c).obj T) ≫
          modulePullbackCompHom B S hS (y ≫ Y) c T ≫ pullbackTransport T e4 =
      modulePullbackCompHom B S hS y c'' ((modulePullback B S hS h).obj T) ≫
        modulePullbackCompHom B S hS (y ≫ c'') h T ≫ pullbackTransport T e3 := by
  have e4' : y ≫ Y ≫ c = Q := (Category.assoc y Y c).symm.trans e4
  have e3' : y ≫ c'' ≫ h = Q := (Category.assoc y c'' h).symm.trans e3
  have I := (modulePullback B S hS y).map_comp (modulePullbackCompInv B S hS Y c T)
    (modulePullbackCompHom B S hS Y c T)
  rewrite [modulePullbackCompInv_comp_compHom, CategoryTheory.Functor.map_id] at I
  rewrite [modulePullback_map_pullbackSquareHom c'' c h Y hY T y, Category.assoc, Category.assoc,
    modulePullbackCompHom_assoc_transport B S hS y Y c T e4 e4', ← reassoc_of% I,
    modulePullback_map_pullbackTransport_comp_compHom_assoc B S hS y hY T,
    pullbackTransport_comp T (congrArg (y ≫ ·) hY) e4' e3',
    ← modulePullbackCompHom_assoc_transport B S hS y c'' h T e3 e3']
  rfl

end Square

/-! ### The canonical transition of an inverse image is the pulled-back canonical transition -/

section Coherence

variable {A : AlgebraicSpaces B S hS} {G G'' : GroupoidInAlgebraicSpaces B S hS A}
  {X'' X : AlgebraicSpaces B S hS} (c'' : G''.objects ⟶ X'') (c : G.objects ⟶ X) (h : X'' ⟶ X)
  (hc'' : G''.target ≫ c'' = G''.source ≫ c'') (hc : G.target ≫ c = G.source ≫ c)
  (Y : G''.objects ⟶ G.objects) (Z : G''.arrows ⟶ G.arrows) (hY : c'' ≫ h = Y ≫ c)
  (hta : G''.target ≫ Y = Z ≫ G.target) (hsb : Z ≫ G.source = G''.source ≫ Y)
  (T : Modules.{u, u} B S hS X.1 X.2)

/-- The reindexing along `Z` of the canonical transition of `c^*𝒯`, read to a common composite,
is a transport. -/
@[reassoc]
theorem modulePullbackReindex_spaceBaseDescent_comp_compHom {Q : G''.arrows ⟶ X}
    (ep : (Z ≫ G.target) ≫ c = Q) (eq : (Z ≫ G.source) ≫ c = Q) :
    modulePullbackReindex Z (spaceBaseDescent B S hS G c hc T) ≫
        modulePullbackCompHom B S hS (Z ≫ G.source) c T ≫ pullbackTransport T eq =
      modulePullbackCompHom B S hS (Z ≫ G.target) c T ≫ pullbackTransport T ep := by
  have H := modulePullbackFlatten'_reindex_spaceBaseDescent B S hS G c hc T Z ep eq rfl
  rewrite [modulePullbackFlatten'_eq_comp, modulePullbackFlatten_eq_compHom B S hS c] at H
  have hrfl : pullbackTransport T (rfl : Q = Q) = 𝟙 _ := rfl
  have H' := congrArg (modulePullbackCompHom B S hS (Z ≫ G.target) c T ≫ pullbackTransport T ep ≫
      ·) H
  have hrfl' : pullbackTransport T (rfl : (Z ≫ G.target) ≫ c = (Z ≫ G.target) ≫ c) = 𝟙 _ := rfl
  rewrite [hrfl, Category.comp_id, ← Category.assoc (pullbackTransport T ep),
    pullbackTransport_comp T ep ep.symm rfl, hrfl', Category.id_comp] at H'
  simp only [Category.assoc] at H'
  rewrite [reassoc_of% (modulePullbackCompHom_comp_compInv B S hS (Z ≫ G.target) c T)] at H'
  simpa only [Category.assoc, Category.id_comp] using H'

/-- **The canonical transition of an inverse image is the pulled-back canonical transition**
(the coherence of Stacks 03LU): for a square `c'' ≫ h = Y ≫ c` and a morphism `(Y, Z)` of the
groupoids compatible with the projections, the identification `c''^*(h^*𝒯) ≅ Y^*(c^*𝒯)` carries
the canonical transition of `c''^*(h^*𝒯)` to the pulled-back canonical transition of `c^*𝒯`. -/
theorem transitionCommutes_pullbackSquareHom :
    TransitionCommutes B S hS (U := G''.objects) (V := G''.arrows) (a := G''.target)
      (b := G''.source) (spaceBaseDescent B S hS G'' c'' hc'' ((modulePullback B S hS h).obj T))
      (pairTransition Y Z hta hsb ((modulePullback B S hS c).obj T)
        (spaceBaseDescent B S hS G c hc T))
      (pullbackSquareHom c'' c h Y hY T) := by
  have eb : (G''.source ≫ c'') ≫ h = (G''.target ≫ c'') ≫ h := by rw [hc'']
  have ebY : (G''.source ≫ Y) ≫ c = (G''.target ≫ c'') ≫ h := by
    rw [Category.assoc, ← hY, ← Category.assoc, eb]
  have eaY : (G''.target ≫ Y) ≫ c = (G''.target ≫ c'') ≫ h := by
    rw [Category.assoc, ← hY, ← Category.assoc]
  have eZq : (Z ≫ G.source) ≫ c = (G''.target ≫ c'') ≫ h := by rw [hsb]; exact ebY
  have eZp : (Z ≫ G.target) ≫ c = (G''.target ≫ c'') ≫ h := by rw [← hta]; exact eaY
  have hrfl : pullbackTransport T (rfl : (G''.source ≫ Y) ≫ c = (G''.source ≫ Y) ≫ c) = 𝟙 _ :=
    rfl
  have hσ : (modulePullbackCompHom B S hS G''.source Y ((modulePullback B S hS c).obj T) ≫
      modulePullbackCompHom B S hS (G''.source ≫ Y) c T ≫ pullbackTransport T ebY) ≫
      (pullbackTransport T ebY.symm ≫ modulePullbackCompInv B S hS (G''.source ≫ Y) c T ≫
        modulePullbackCompInv B S hS G''.source Y ((modulePullback B S hS c).obj T)) = 𝟙 _ := by
    rewrite [Category.assoc, Category.assoc, ← Category.assoc (pullbackTransport T ebY),
      pullbackTransport_comp T ebY ebY.symm rfl, hrfl, Category.id_comp,
      reassoc_of% (modulePullbackCompHom_comp_compInv B S hS (G''.source ≫ Y) c T)]
    exact modulePullbackCompHom_comp_compInv B S hS G''.source Y _
  refine transitionSquare_of_readings (modulePullback B S hS G''.target)
    (modulePullback B S hS G''.source)
    (spaceBaseDescent B S hS G'' c'' hc'' ((modulePullback B S hS h).obj T))
    (pairTransition Y Z hta hsb ((modulePullback B S hS c).obj T)
      (spaceBaseDescent B S hS G c hc T)) (pullbackSquareHom c'' c h Y hY T)
    (modulePullbackCompHom B S hS G''.target c'' ((modulePullback B S hS h).obj T) ≫
      modulePullbackCompHom B S hS (G''.target ≫ c'') h T ≫ pullbackTransport T rfl)
    (modulePullbackCompHom B S hS G''.source c'' ((modulePullback B S hS h).obj T) ≫
      modulePullbackCompHom B S hS (G''.source ≫ c'') h T ≫ pullbackTransport T eb)
    (modulePullbackCompHom B S hS G''.target Y ((modulePullback B S hS c).obj T) ≫
      modulePullbackCompHom B S hS (G''.target ≫ Y) c T ≫ pullbackTransport T eaY)
    (modulePullbackCompHom B S hS G''.source Y ((modulePullback B S hS c).obj T) ≫
      modulePullbackCompHom B S hS (G''.source ≫ Y) c T ≫ pullbackTransport T ebY)
    (pullbackTransport T ebY.symm ≫ modulePullbackCompInv B S hS (G''.source ≫ Y) c T ≫
      modulePullbackCompInv B S hS G''.source Y ((modulePullback B S hS c).obj T))
    hσ ?_ ?_ ?_ ?_
  · exact modulePullbackUnflatten_pullbackTransport_comp_compHom B S hS _ _ c'' hc'' h T rfl eb
  · rewrite [pairTransition_comp_compHom_assoc Y Z hta hsb _ _,
      pullbackTransport_comp_compHom_assoc B S hS c hsb T,
      pullbackTransport_comp T (congrArg (· ≫ c) hsb) ebY eZq,
      modulePullbackReindex_spaceBaseDescent_comp_compHom c hc Z T eZp eZq,
      pullbackTransport_comp_compHom_assoc B S hS c hta T,
      pullbackTransport_comp T (congrArg (· ≫ c) hta) eZp eaY]
    rfl
  · exact modulePullback_map_pullbackSquareHom_comp_compHom c'' c h Y hY T G''.target rfl eaY
  · exact modulePullback_map_pullbackSquareHom_comp_compHom c'' c h Y hY T G''.source eb ebY

/-- `AlgebraicGeometry.Space.transitionCommutes_pullbackSquareHom`, followed by a further
compatibility. -/
theorem transitionCommutes_pullbackSquareHom_comp {N : Modules.{u, u} B S hS G''.objects.1
    G''.objects.2}
    (β : (modulePullback B S hS G''.target).obj N ⟶ (modulePullback B S hS G''.source).obj N)
    (g : (modulePullback B S hS Y).obj ((modulePullback B S hS c).obj T) ⟶ N)
    (hg : TransitionCommutes B S hS (U := G''.objects) (V := G''.arrows) (a := G''.target)
      (b := G''.source) (pairTransition Y Z hta hsb ((modulePullback B S hS c).obj T)
        (spaceBaseDescent B S hS G c hc T)) β g) :
    TransitionCommutes B S hS (U := G''.objects) (V := G''.arrows) (a := G''.target)
      (b := G''.source) (spaceBaseDescent B S hS G'' c'' hc'' ((modulePullback B S hS h).obj T))
      β (pullbackSquareHom c'' c h Y hY T ≫ g) :=
  transitionSquare_comp (modulePullback B S hS G''.target) (modulePullback B S hS G''.source) _ _ _
    _ _ (transitionCommutes_pullbackSquareHom c'' c h hc'' hc Y Z hY hta hsb T) hg

end Coherence

/-! ### The pulled-back transition of a scheme transition -/

section Represented

variable (B S hS)

/-- The contraction of the inverse images along two represented morphisms, at a module, is the
comparison of Stacks 03LU followed by the transport to the represented composite. -/
theorem representedModulePullbackCompIso_app_hom_eq {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) (F : Modules.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2) :
    ((representedModulePullbackCompIso B S hS h g).app F).hom =
      modulePullbackCompHom B S hS (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
          F ≫ pullbackTransport F (representedSpaceMap_comp B S hS h g) := by
  rw [NatIso.trans_app, Iso.trans_hom, eqToIso_modulePullback_app_hom]
  rfl

/-- `AlgebraicGeometry.Space.representedSpaceMap_comp`, with the composite formed in the category
of algebraic spaces. -/
theorem algebraicSpacesComp_representedSpaceMap {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) :
    @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g) = representedSpaceMap B S hS (h ≫ g) :=
  representedSpaceMap_comp B S hS h g

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` composes**, in the form read through
`AlgebraicGeometry.Space.modulePullbackCompHom`. -/
theorem compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom {W V U : BigFppfOver B S hS}
    (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    modulePullbackCompHom B S hS (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≫
      pullbackTransport _ (algebraicSpacesComp_representedSpaceMap B S hS h g) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M).hom =
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS h
        (quasicoherentPullbackObj B S hS g M)).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
          (quasicoherentPullbackCompIso B S hS h g M).hom).hom := by
  have H := congrArg Iso.hom (modulePullbackRepresentedQuasicoherentIso_comp B S hS h g M)
  refine Eq.trans ?_ (H.trans ?_)
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M).hom)
        (representedModulePullbackCompIso_app_hom_eq B S hS h g _).symm)).trans
      (Iso.trans_hom _ _).symm
  · exact (Iso.trans_hom _ _).trans (congrArg (_ ≫ ·) (Iso.trans_hom _ _))

/-- The identification `k₁^*M ⟶ k₂^*M` of the pullbacks of a quasi-coherent module along two
equal morphisms of the site. -/
def quasicoherentPullbackEqToHom {V U : BigFppfOver B S hS} {k₁ k₂ : V ⟶ U} (e : k₁ = k₂)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackObj B S hS k₁ M ⟶ quasicoherentPullbackObj B S hS k₂ M :=
  eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) e)

/-- The transport of a quasi-coherent inverse image along `rfl : k₁ = k₁` is the identity. -/
theorem quasicoherentPullbackEqToHom_rfl {V U : BigFppfOver B S hS} {k₁ : V ⟶ U}
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackEqToHom B S hS (rfl : k₁ = k₁) M = 𝟙 _ :=
  eqToHom_refl _ _

/-- The module attached to the identity of the pullback of a quasi-coherent module. -/
theorem representedQuasicoherentSchemeEquivalence_map_id_hom {V U : BigFppfOver B S hS}
    {k : V ⟶ U} (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (𝟙 (quasicoherentPullbackObj B S hS k M))).hom = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The identification of the inverse images of `M^a` along two equal represented morphisms is
the module attached to the identification of the pullbacks of `M`.** -/
theorem pullbackTransport_comp_modulePullbackRepresentedQuasicoherentIso_hom
    {V U : BigFppfOver B S hS} {k₁ k₂ : V ⟶ U} (e : k₁ = k₂)
    (e' : representedSpaceMap B S hS k₁ = representedSpaceMap B S hS k₂)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    pullbackTransport _ e' ≫ (modulePullbackRepresentedQuasicoherentIso B S hS k₂ M).hom =
      (modulePullbackRepresentedQuasicoherentIso B S hS k₁ M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
          (quasicoherentPullbackEqToHom B S hS e M)).hom := by
  subst e
  have h1 : pullbackTransport ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
      M).obj
      e' = 𝟙 _ := rfl
  have h2 := representedQuasicoherentSchemeEquivalence_map_id_hom B S hS (k := k₁) M
  rw [quasicoherentPullbackEqToHom_rfl]
  exact (congrArg (· ≫ _) h1).trans ((Category.id_comp _).trans
    ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) h2.symm)))

variable {U'' R'' U R : BigFppfOver B S hS} {t'' s'' : R'' ⟶ U''} {t s : R ⟶ U}
  (yU : U'' ⟶ U) (yR : R'' ⟶ R) (hta : t'' ≫ yU = yR ≫ t) (hsb : yR ≫ s = s'' ≫ yU)
  (M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)

/-- The reindexing of a scheme transition `τ : t^*M ⟶ s^*M` along `yR`, read between the
squares `t'' ≫ yU = yR ≫ t` and `yR ≫ s = s'' ≫ yU`. -/
def schemePairReindex :
    quasicoherentPullbackObj B S hS (t'' ≫ yU) M ⟶ quasicoherentPullbackObj B S hS (s'' ≫ yU) M :=
  quasicoherentPullbackEqToHom B S hS hta M ≫ schemeTransitionReindex B S hS t s M τ yR ≫
    quasicoherentPullbackEqToHom B S hS hsb M

/-- `schemePairReindex` is the composite of the transport along `hta`, the reindexing of `τ`
along `yR`, and the transport along `hsb`. -/
theorem schemePairReindex_eq :
    schemePairReindex B S hS yU yR hta hsb M τ =
      quasicoherentPullbackEqToHom B S hS hta M ≫ schemeTransitionReindex B S hS t s M τ yR ≫
        quasicoherentPullbackEqToHom B S hS hsb M :=
  rfl

/-- **The pulled-back scheme transition**: a scheme transition `τ : t^*M ⟶ s^*M` on `R`, read on
`R''` as a transition of `yU^*M` through `t'' ≫ yU = yR ≫ t` and `yR ≫ s = s'' ≫ yU`. -/
def schemePairTransition :
    quasicoherentPullbackObj B S hS t'' (quasicoherentPullbackObj B S hS yU M) ⟶
      quasicoherentPullbackObj B S hS s'' (quasicoherentPullbackObj B S hS yU M) :=
  (quasicoherentPullbackCompIso B S hS t'' yU M).hom ≫ schemePairReindex B S hS yU yR hta hsb M τ ≫
    (quasicoherentPullbackCompIso B S hS s'' yU M).inv

/-- `schemePairTransition` is `schemePairReindex` conjugated by the composition isomorphisms
`quasicoherentPullbackCompIso` along `(t'', yU)` and `(s'', yU)`. -/
theorem schemePairTransition_eq :
    schemePairTransition B S hS yU yR hta hsb M τ =
      (quasicoherentPullbackCompIso B S hS t'' yU M).hom ≫
        schemePairReindex B S hS yU yR hta hsb M τ ≫
          (quasicoherentPullbackCompIso B S hS s'' yU M).inv :=
  rfl

/-- The module attached to a morphism that is a threefold composite is the threefold composite of
the modules attached to the factors. -/
private theorem representedEquivalence_map_hom_comp₃ {V : BigFppfOver B S hS}
    {A₀ A₁ A₂ A₃ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {x : A₀ ⟶ A₃} {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} (e : x = a ≫ b ≫ c) :
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map x).hom =
      ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map a).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map b).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map c).hom := by
  subst e
  exact (congrArg InducedCategory.Hom.hom
    (((representedQuasicoherentSchemeEquivalence B S hS V).functor.map_comp _ _).trans
      (congrArg (_ ≫ ·) ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map_comp _
        _)))).trans rfl

/-- The abstract shape of `transitionCommutes_pairTransition_representedSchemeTransition`, at
variables. -/
theorem transition_of_pair_core {D : Type*} [Category D]
    {X0 X1 Pa Pb Qt Qs W W' NkT NkS V V' : D} (pairT : X0 ⟶ X1) (mb : X1 ⟶ Pb) (ma : X0 ⟶ Pa)
    (C3t : Pa ⟶ Qt) (Aσ : Qt ⟶ Qs) (C3sinv : Qs ⟶ Pb) (C3s : Pb ⟶ Qs) (cHb : X1 ⟶ W)
    (pTs : W ⟶ W') (c3kS : W' ⟶ NkS) (cHa : X0 ⟶ V) (pTt : V ⟶ V') (c3kT : V' ⟶ NkT)
    (Aω : NkT ⟶ NkS) (Ait : Qt ⟶ NkT) (Ais : Qs ⟶ NkS) (Aisinv : NkS ⟶ Qs)
    (core : pairT ≫ cHb ≫ pTs ≫ c3kS = cHa ≫ pTt ≫ c3kT ≫ Aω)
    (Et : cHa ≫ pTt ≫ c3kT = ma ≫ C3t ≫ Ait) (Es : cHb ≫ pTs ≫ c3kS = mb ≫ C3s ≫ Ais)
    (hσ : Aσ = Ait ≫ Aω ≫ Aisinv) (hAis : Ais ≫ Aisinv = 𝟙 Qs) (hC3 : C3s ≫ C3sinv = 𝟙 Pb) :
    pairT ≫ mb = ma ≫ C3t ≫ Aσ ≫ C3sinv := by
  have h1 : pairT ≫ mb = (pairT ≫ cHb ≫ pTs ≫ c3kS) ≫ Aisinv ≫ C3sinv := by
    rw [Es]
    simp only [Category.assoc, reassoc_of% hAis, hC3, Category.comp_id]
  have h2 : cHa ≫ pTt ≫ c3kT ≫ Aω ≫ Aisinv ≫ C3sinv =
      ma ≫ C3t ≫ Ait ≫ Aω ≫ Aisinv ≫ C3sinv := by
    simpa only [Category.assoc] using congrArg (· ≫ Aω ≫ Aisinv ≫ C3sinv) Et
  rw [h1, core]
  simp only [Category.assoc]
  rw [h2, hσ]
  simp only [Category.assoc]

/-- **The pulled-back transition of `τ^a` is the transition attached to the pulled-back scheme
transition**: the identification `yU^*(M^a) ≅ (yU^*M)^a` carries the transition morphism `τ^a`,
pulled back along `(yU, yR)`, to `σ^a` for the pulled-back scheme transition `σ`. -/
theorem transitionCommutes_pairTransition_representedSchemeTransition :
    TransitionCommutes B S hS (a := representedSpaceMap B S hS t'')
      (b := representedSpaceMap B S hS s'')
      (pairTransition (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        (representedSchemeTransition B S hS t s M τ))
      (representedSchemeTransition B S hS t'' s'' (quasicoherentPullbackObj B S hS yU M)
        (schemePairTransition B S hS yU yR hta hsb M τ))
      (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom := by
  have es : representedSpaceMap B S hS (yR ≫ s) = representedSpaceMap B S hS (s'' ≫ yU) :=
    congrArg (representedSpaceMap B S hS) hsb
  have et : representedSpaceMap B S hS (t'' ≫ yU) = representedSpaceMap B S hS (yR ≫ t) :=
    congrArg (representedSpaceMap B S hS) hta
  have hR := (transitionReindex_eq_modulePullbackReindex
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (V := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩)
      (W := ⟨yoneda.obj R'', isAlgebraicSpace_yoneda B S hS R''⟩)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      (representedSchemeTransition B S hS t s M τ) (representedSpaceMap B S hS yR)).symm.trans
    (transitionReindex_representedSchemeTransition B S hS t s M τ yR)
  have hP7 := representedEquivalence_map_hom_comp₃ B S hS (V := R'')
    (schemePairReindex_eq B S hS yU yR hta hsb M τ)
  have core := pairTransition_comp_of_readings (representedSpaceMap B S hS yU)
    (representedSpaceMap B S hS yR) (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
    (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb) ((representedQuasicoherentSchemeEquivalence
        B S hS U).functor.obj M).obj
    (representedSchemeTransition B S hS t s M τ)
    (algebraicSpacesComp_representedSpaceMap B S hS t'' yU)
    (algebraicSpacesComp_representedSpaceMap B S hS s'' yU) (representedSpaceMap_comp B S hS yR t)
    (representedSpaceMap_comp B S hS yR s) et es
    (modulePullbackRepresentedQuasicoherentIso B S hS (t'' ≫ yU) M).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS (s'' ≫ yU) M).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS (yR ≫ t) M).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS (yR ≫ s) M).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS (yR ≫ s) M).inv
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map (schemeTransitionReindex B
        S hS t s M τ yR)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
        (quasicoherentPullbackEqToHom B S hS hsb M)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
        (quasicoherentPullbackEqToHom B S hS hta M)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map (schemePairReindex B S hS
        yU yR hta hsb M τ)).hom hR
    (pullbackTransport_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS hsb es M)
    (modulePullbackRepresentedQuasicoherentIso B S hS (yR ≫ s) M).inv_hom_id
    (pullbackTransport_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS hta et M) hP7
  have hσ := representedEquivalence_map_hom_comp₃ B S hS (V := R'')
    (schemePairTransition_eq B S hS yU yR hta hsb M τ)
  have hAis : ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
      (quasicoherentPullbackCompIso B S hS s'' yU M).hom).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
          (quasicoherentPullbackCompIso B S hS s'' yU M).inv).hom = 𝟙 _ :=
    (congrArg InducedCategory.Hom.hom (((representedQuasicoherentSchemeEquivalence B S hS
        R'').functor.map_comp _ _).symm.trans
      ((congrArg (representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
          (quasicoherentPullbackCompIso B S hS s'' yU M).hom_inv_id).trans
        ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map_id _)))).trans rfl
  unfold TransitionCommutes representedSchemeTransition
  exact transition_of_pair_core
    (pairTransition (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
      (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
      (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      (representedSchemeTransition B S hS t s M τ))
    ((modulePullback B S hS (representedSpaceMap B S hS s'')).map
      (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom)
    ((modulePullback B S hS (representedSpaceMap B S hS t'')).map
      (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom)
    (modulePullbackRepresentedQuasicoherentIso B S hS t'' (quasicoherentPullbackObj B S hS yU
        M)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map (schemePairTransition B S
        hS yU yR hta hsb M τ)).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS s'' (quasicoherentPullbackObj B S hS yU
        M)).inv
    (modulePullbackRepresentedQuasicoherentIso B S hS s'' (quasicoherentPullbackObj B S hS yU
        M)).hom
    _ _ _ _ _ _
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map (schemePairReindex B S hS
        yU yR hta hsb M τ)).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
        (quasicoherentPullbackCompIso B S hS t'' yU M).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
        (quasicoherentPullbackCompIso B S hS s'' yU M).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS R'').functor.map
        (quasicoherentPullbackCompIso B S hS s'' yU M).inv).hom core
    (compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS t'' yU M)
    (compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS s'' yU M) hσ hAis
    (modulePullbackRepresentedQuasicoherentIso B S hS s'' (quasicoherentPullbackObj B S hS yU
        M)).hom_inv_id

end Represented

/-! ### The descended isomorphism -/

section Descent

variable {X'' : AlgebraicSpaces B S hS} (P'' : Presentation B S hS X''.obj X''.property)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P''.U).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS P''.target M'' ⟶
    quasicoherentPullbackObj B S hS P''.source M'')
  (hc'' : PresentationSchemeCocycle P'' M'' τ'') (hu'' : PresentationSchemeUnit P'' M'' τ'')
  (Y : QuasicoherentSheaves.{u, u} B S hS X''.obj X''.property)
  (χ : (modulePullback B S hS (presentationAtlas P'')).obj Y.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj)
  (hχ : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
    (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
    (b := (presentationGroupoid P'').source)
    (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
      (presentationAtlas_comm P'') Y.obj)
    (presentationSchemeTransition P'' M'' τ'') χ.hom)

/-- An isomorphism of the underlying modules of two quasi-coherent modules on a groupoid,
compatible with the transitions, is an isomorphism of quasi-coherent modules on the groupoid. -/
def QuasicoherentModule.isoMk {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}
    {M N : QuasicoherentModule B S hS G} (e : M.F.obj ≅ N.F.obj)
    (he : QuasicoherentModule.Compatible e.hom) : M ≅ N where
  hom := QuasicoherentModule.homMk e.hom he
  inv := QuasicoherentModule.homMk e.inv
    ((QuasicoherentModule.compatible_iff_transitionCommutes B S hS _).2
      (transitionSquare_symm (modulePullback B S hS G.target) (modulePullback B S hS G.source)
        M.alpha N.alpha e ((QuasicoherentModule.compatible_iff_transitionCommutes B S hS _).1 he)))
  hom_inv_id := QuasicoherentModule.Hom.ext (by
    rw [QuasicoherentModule.comp_hom, QuasicoherentModule.homMk_hom,
      QuasicoherentModule.homMk_hom, e.hom_inv_id, QuasicoherentModule.id_hom])
  inv_hom_id := QuasicoherentModule.Hom.ext (by
    rw [QuasicoherentModule.comp_hom, QuasicoherentModule.homMk_hom,
      QuasicoherentModule.homMk_hom, e.inv_hom_id, QuasicoherentModule.id_hom])

/-- The underlying morphism of the forward morphism of `QuasicoherentModule.isoMk e he` is
`e.hom`. -/
theorem QuasicoherentModule.isoMk_hom_hom {A : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS A} {M N : QuasicoherentModule B S hS G}
    (e : M.F.obj ≅ N.F.obj) (he : QuasicoherentModule.Compatible e.hom) :
    (QuasicoherentModule.isoMk e he).hom.hom = e.hom :=
  QuasicoherentModule.homMk_hom _ _

include hχ in
/-- The isomorphism of the groupoid modules of `𝒴` and of `D(M'')` attached to `χ`. -/
def presentationDescendedGroupoidIso :
    (presentationQuasicoherentEquivalence P'').functor.obj Y ≅
      (presentationQuasicoherentEquivalence P'').functor.obj
        (presentationDescendedModule P'' M'' τ'' hc'' hu'') :=
  QuasicoherentModule.isoMk (χ ≪≫ (presentationDescendedModuleChartIso P'' M'' τ'' hc'' hu'').symm)
    (presentationDescendedIntoChartHom_compatible P'' τ'' hc'' hu'' Y χ.hom hχ)

include hχ in
/-- The underlying morphism of the forward morphism of `presentationDescendedGroupoidIso` is
`χ.hom` followed by the inverse of `presentationDescendedModuleChartIso`. -/
theorem presentationDescendedGroupoidIso_hom_hom :
    (presentationDescendedGroupoidIso P'' τ'' hc'' hu'' Y χ hχ).hom.hom =
      χ.hom ≫ (presentationDescendedModuleChartIso P'' M'' τ'' hc'' hu'').inv :=
  (QuasicoherentModule.isoMk_hom_hom _ _).trans
    ((Iso.trans_hom _ _).trans (congrArg (χ.hom ≫ ·) (Iso.symm_hom _)))

/-- The underlying morphism of `presentationDescendedIntoGroupoidHom` is `χ.hom` followed by the
inverse of `presentationDescendedModuleChartIso`. -/
theorem presentationDescendedIntoGroupoidHom_hom :
    (presentationDescendedIntoGroupoidHom P'' τ'' hc'' hu'' Y χ.hom hχ).hom =
      χ.hom ≫ (presentationDescendedModuleChartIso P'' M'' τ'' hc'' hu'').inv := by
  unfold presentationDescendedIntoGroupoidHom
  exact (QuasicoherentModule.homMk_hom _ _).trans
    (presentationDescendedIntoChartHom_eq P'' τ'' hc'' hu'' Y χ.hom)

/-- The forward morphism of `presentationDescendedGroupoidIso` is
`presentationDescendedIntoGroupoidHom`. -/
theorem presentationDescendedGroupoidIso_hom :
    (presentationDescendedGroupoidIso P'' τ'' hc'' hu'' Y χ hχ).hom =
      presentationDescendedIntoGroupoidHom P'' τ'' hc'' hu'' Y χ.hom hχ :=
  QuasicoherentModule.Hom.ext ((presentationDescendedGroupoidIso_hom_hom P'' τ'' hc'' hu'' Y χ
      hχ).trans
    (presentationDescendedIntoGroupoidHom_hom P'' τ'' hc'' hu'' Y χ hχ).symm)

/-- The morphism `presentationDescendedIntoQuasicoherentHom` is an isomorphism. -/
instance isIso_presentationDescendedIntoQuasicoherentHom :
    IsIso (presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ) := by
  have : IsIso ((presentationQuasicoherentEquivalence P'').functor.map
      (presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ)) := by
    rewrite [functor_map_presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ,
      ← presentationDescendedGroupoidIso_hom P'' τ'' hc'' hu'' Y χ hχ]
    exact Iso.isIso_hom _
  exact isIso_of_reflects_iso _ (presentationQuasicoherentEquivalence P'').functor

/-- **Descent of an isomorphism into a descended module along a presentation**: an isomorphism
`χ : φ^*𝒴 ≅ M''^a` on the atlas of a presentation, carrying the canonical transition of `φ^*𝒴`
to the transition `τ''^a`, descends to an isomorphism `𝒴 ≅ D(M'')` of quasi-coherent modules. -/
def presentationDescendedIso : Y ≅ presentationDescendedModule P'' M'' τ'' hc'' hu'' :=
  asIso (presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ)

/-- The forward morphism of `presentationDescendedIso` is
`presentationDescendedIntoQuasicoherentHom`. -/
theorem presentationDescendedIso_hom : (presentationDescendedIso P'' τ'' hc'' hu'' Y χ hχ).hom =
    presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ :=
  asIso_hom (presentationDescendedIntoQuasicoherentHom P'' τ'' hc'' hu'' Y χ.hom hχ)

/-- **The inverse image along the atlas of the descended isomorphism is `χ`**, through the chart
identification of `D(M'')`. -/
theorem presentationDescendedIso_spec :
    (modulePullback B S hS (presentationAtlas P'')).map
        (presentationDescendedIso P'' τ'' hc'' hu'' Y χ hχ).hom.hom ≫
      (presentationDescendedModuleChartIso P'' M'' τ'' hc'' hu'').hom = χ.hom := by
  rewrite [presentationDescendedIso_hom P'' τ'' hc'' hu'' Y χ hχ]
  exact presentationDescendedIntoHom_spec P'' τ'' hc'' hu'' Y χ.hom hχ

section OfEq

variable (φ : (modulePullback B S hS (presentationAtlas P'')).obj Y.obj ⟶
    ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj)
  (hφ : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
    (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
    (b := (presentationGroupoid P'').source)
    (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
      (presentationAtlas_comm P'') Y.obj)
    (presentationSchemeTransition P'' M'' τ'') φ)
  (hχφ : χ.hom = φ)

include hφ hχφ in
/-- If `φ` commutes with the transitions and `χ.hom = φ`, then `χ.hom` commutes with the
transitions. -/
theorem transitionCommutes_hom_of_eq :
    TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
      (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
      (b := (presentationGroupoid P'').source)
      (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
        (presentationAtlas_comm P'') Y.obj)
      (presentationSchemeTransition P'' M'' τ'') χ.hom :=
  hχφ.symm ▸ hφ

end OfEq

end Descent

/-! ### The inverse image of a descended module along a morphism of presentations -/

section PullbackDescent

variable {X'' X : AlgebraicSpaces B S hS} (P'' : Presentation B S hS X''.obj X''.property)
  (P : Presentation B S hS X.obj X.property) (h : X'' ⟶ X) (yU : P''.U ⟶ P.U) (yR : P''.R ⟶ P.R)
  (hY : presentationAtlas P'' ≫ h = representedSpaceMap B S hS yU ≫ presentationAtlas P)
  (hta : P''.target ≫ yU = yR ≫ P.target) (hsb : yR ≫ P.source = P''.source ≫ yU)
  (T : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (κ : (modulePullback B S hS (presentationAtlas P)).obj T.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) T.obj)
    (presentationSchemeTransition P M τ) κ.hom)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P''.U).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS P''.target M'' ⟶
    quasicoherentPullbackObj B S hS P''.source M'')
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (hΘ : schemePairTransition B S hS yU yR hta hsb M τ ≫
      quasicoherentPullbackMap B S hS P''.source Θ.hom =
    quasicoherentPullbackMap B S hS P''.target Θ.hom ≫ τ'')

include hκ hΘ in
/-- **The identification on the atlas carries the canonical transition of `c''^*(h^*𝒯)` to
`τ''^a`.** -/
theorem transitionCommutes_presentationPullbackChartHom :
    TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
      (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
      (b := (presentationGroupoid P'').source)
      (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
        (presentationAtlas_comm P'') ((modulePullback B S hS h).obj T.obj))
      (presentationSchemeTransition P'' M'' τ'')
      (pullbackSquareHom (presentationAtlas P'') (presentationAtlas P) h
          (representedSpaceMap B S hS yU) hY T.obj ≫
        (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y :=
            (presentationGroupoid P).objects)
          (representedSpaceMap B S hS yU)).map κ.hom ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map Θ.hom).hom) := by
  have T1 := transitionCommutes_pullbackSquareHom (G := presentationGroupoid P)
    (G'' := presentationGroupoid P'') (presentationAtlas P'') (presentationAtlas P) h
    (presentationAtlas_comm P'') (presentationAtlas_comm P) (representedSpaceMap B S hS yU)
    (representedSpaceMap B S hS yR) hY (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
    (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb) T.obj
  have T2 : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects) (V :=
      (presentationGroupoid P'').arrows)
      (a := (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source)
          (pairTransition (a := (presentationGroupoid P'').target) (b := (presentationGroupoid
          P'').source) (p := (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb) ((modulePullback B S hS
            (presentationAtlas P)).obj T.obj) (spaceBaseDescent B S hS (presentationGroupoid P)
            (presentationAtlas P) (presentationAtlas_comm P) T.obj)) (pairTransition (a :=
            (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source) (p :=
            (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
            ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
            (presentationSchemeTransition P M τ)) ((modulePullback B S hS (X :=
            (presentationGroupoid P'').objects) (Y := (presentationGroupoid P).objects)
        (representedSpaceMap B S hS yU)).map κ.hom) :=
    pairTransition_naturality (a := (presentationGroupoid P'').target) (b := (presentationGroupoid
        P'').source) (p := (presentationGroupoid P).target)
      (q := (presentationGroupoid P).source) (representedSpaceMap B S hS yU)
      (representedSpaceMap B S hS yR) (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
      (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
      (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
          (presentationAtlas_comm P) T.obj)
      (presentationSchemeTransition P M τ) κ.hom hκ
  have T3 : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects) (V :=
      (presentationGroupoid P'').arrows)
      (a := (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source)
      (pairTransition (a := (presentationGroupoid P'').target) (b := (presentationGroupoid
          P'').source) (p := (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
            ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
        (presentationSchemeTransition P M τ))
      (presentationSchemeTransition P'' (quasicoherentPullbackObj B S hS yU M)
          (schemePairTransition B S hS yU yR hta hsb M τ))
      (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom :=
    transitionCommutes_pairTransition_representedSchemeTransition B S hS yU yR hta hsb M τ
  have T4 : TransitionCommutes B S hS (U := (presentationGroupoid P'').objects) (V :=
      (presentationGroupoid P'').arrows)
      (a := (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source)
      (presentationSchemeTransition P'' (quasicoherentPullbackObj B S hS yU M)
          (schemePairTransition B S hS yU yR hta hsb M τ))
      (presentationSchemeTransition P'' M'' τ'')
      ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map Θ.hom).hom :=
    representedSchemeTransition_naturality B S hS P''.target P''.source (quasicoherentPullbackObj B
        S hS yU M)
      (schemePairTransition B S hS yU yR hta hsb M τ) τ'' Θ.hom hΘ
  have T34 := transitionSquare_comp (modulePullback B S hS (presentationGroupoid P'').target)
      (modulePullback B S hS (presentationGroupoid P'').source) (pairTransition (a :=
      (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source) (p :=
      (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
            ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
            (presentationSchemeTransition P M τ)) (presentationSchemeTransition P''
            (quasicoherentPullbackObj B S hS yU M) (schemePairTransition B S hS yU yR hta hsb M τ))
            (presentationSchemeTransition P'' M'' τ'') (modulePullbackRepresentedQuasicoherentIso B
            S hS yU M).hom ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map
            Θ.hom).hom T3 T4
  have T234 := transitionSquare_comp (modulePullback B S hS (presentationGroupoid P'').target)
      (modulePullback B S hS (presentationGroupoid P'').source) (pairTransition (a :=
      (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source) (p :=
      (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb) ((modulePullback B S hS
            (presentationAtlas P)).obj T.obj) (spaceBaseDescent B S hS (presentationGroupoid P)
            (presentationAtlas P) (presentationAtlas_comm P) T.obj)) (pairTransition (a :=
            (presentationGroupoid P'').target) (b := (presentationGroupoid P'').source) (p :=
            (presentationGroupoid P).target) (q := (presentationGroupoid P).source)
        (representedSpaceMap B S hS yU) (representedSpaceMap B S hS yR)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
        (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb)
            ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
            (presentationSchemeTransition P M τ)) (presentationSchemeTransition P'' M'' τ'')
            ((modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y :=
            (presentationGroupoid P).objects)
        (representedSpaceMap B S hS yU)).map κ.hom) ((modulePullbackRepresentedQuasicoherentIso B S
            hS yU M).hom ≫ ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map
            Θ.hom).hom) T2 T34
  exact transitionCommutes_pullbackSquareHom_comp (G := presentationGroupoid P)
    (G'' := presentationGroupoid P'') (presentationAtlas P'') (presentationAtlas P) h
    (presentationAtlas_comm P'') (presentationAtlas_comm P) (representedSpaceMap B S hS yU)
    (representedSpaceMap B S hS yR) hY (representedSpaceMap_comp_eq_of_comp_eq B S hS hta)
    (representedSpaceMap_comp_eq_of_comp_eq B S hS hsb) T.obj _ _ T234

/-- The identification on the atlas of `X''` of the inverse image `h^*𝒯` with `M''^a`:
`c''^*(h^*𝒯) ≅ yU^*(c^*𝒯) ≅ yU^*(M^a) ≅ (yU^*M)^a ≅ M''^a`. -/
abbrev presentationPullbackChartHom :
    (modulePullback B S hS (presentationAtlas P'')).obj ((modulePullback B S hS h).obj T.obj) ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj :=
  pullbackSquareHom (presentationAtlas P'') (presentationAtlas P) h
      (representedSpaceMap B S hS yU) hY T.obj ≫
    (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y := (presentationGroupoid
        P).objects)
      (representedSpaceMap B S hS yU)).map κ.hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map Θ.hom).hom

/-- The identification on the atlas, as an isomorphism. -/
def presentationPullbackChartIso :
    (modulePullback B S hS (presentationAtlas P'')).obj ((modulePullback B S hS h).obj T.obj) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.obj M'').obj :=
  pullbackSquareIso (presentationAtlas P'') (presentationAtlas P) h
      (representedSpaceMap B S hS yU) hY T.obj ≪≫
    (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y := (presentationGroupoid
        P).objects)
      (representedSpaceMap B S hS yU)).mapIso κ ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS yU M ≪≫
        (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
            P''.U).functor.mapIso Θ)

/-- The forward morphism of `presentationPullbackChartIso` is `presentationPullbackChartHom`. -/
theorem presentationPullbackChartIso_hom :
    (presentationPullbackChartIso P'' P h yU hY T κ Θ).hom =
      presentationPullbackChartHom P'' P h yU hY T κ Θ :=
  (Iso.trans_hom _ _).trans (congrArg (_ ≫ ·) ((Iso.trans_hom _ _).trans
    (congrArg (_ ≫ ·) (Iso.trans_hom _ _))))

end PullbackDescent

end AlgebraicGeometry.Space

end
