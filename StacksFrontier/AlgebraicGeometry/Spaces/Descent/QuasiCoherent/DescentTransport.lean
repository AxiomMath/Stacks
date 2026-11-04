module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPullback

/-!
# Transport of a canonical descent datum along an isomorphism of inverse images

Let `π : U ⟶ Z` and `u : U ⟶ Y` be morphisms of algebraic spaces, `ℳ` a module on `Z`, `𝒢` a
module on `Y`, and `ι : π^*ℳ ≅ u^*𝒢`. For two morphisms `x, y : P ⟶ U` with `x ≫ u = y ≫ u`,
the canonical identification of the two inverse images of `𝒢` to `P`, read through `ι`, is a
morphism `(x ≫ π)^*ℳ ⟶ (y ≫ π)^*ℳ`. These morphisms compose, are the identity on the
diagonal, and are compatible with reindexing along any morphism `P' ⟶ P`: they form the
descent datum of `𝒢` along `u`, transported to `ℳ`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackReindexHom`: the inverse image along `f` of a morphism
  between inverse images of two modules, read between the inverse images along the composites.
* `AlgebraicGeometry.Space.descentTransport`: the transported identification.

## Main results

* `AlgebraicGeometry.Space.descentTransport_comp`: the transported identifications compose.
* `AlgebraicGeometry.Space.descentTransport_self`: on the diagonal the transported identification
  is the identification of the two inverse images.
* `AlgebraicGeometry.Space.modulePullbackReindex_descentTransport`: the transported
  identifications are compatible with reindexing.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Reindexing morphisms between inverse images of two modules -/

section ReindexHom

variable {X Y Z Z' : AlgebraicSpaces B S hS}

/-- The inverse image along `f` of a morphism `a^*ℳ ⟶ b^*𝒩`, read through the comparisons of
Stacks 03LU as a morphism `(f ≫ a)^*ℳ ⟶ (f ≫ b)^*𝒩`. -/
def modulePullbackReindexHom (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    (modulePullback B S hS (f ≫ a)).obj M ⟶ (modulePullback B S hS (f ≫ b)).obj N :=
  (modulePullbackCompIso B S hS f a).inv.app M ≫ (modulePullback B S hS f).map α ≫
    (modulePullbackCompIso B S hS f b).hom.app N

/-- For a single module this is `AlgebraicGeometry.Space.modulePullbackReindex`. -/
theorem modulePullbackReindexHom_eq (f : X ⟶ Y) {a b : Y ⟶ Z}
    {M : Modules.{u, u} B S hS Z.1 Z.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    modulePullbackReindexHom f α = modulePullbackReindex f α :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackReindexHom` as a composite. -/
theorem modulePullbackReindexHom_def (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N) :
    modulePullbackReindexHom f α = (modulePullbackCompIso B S hS f a).inv.app M ≫
      (modulePullback B S hS f).map α ≫ (modulePullbackCompIso B S hS f b).hom.app N :=
  rfl

/-- A morphism `f^*a^*ℳ ⟶ f^*b^*𝒩`, read through the comparisons of Stacks 03LU as a morphism
`(f ≫ a)^*ℳ ⟶ (f ≫ b)^*𝒩`. -/
def modulePullbackFlattenHom (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ψ : (modulePullback B S hS f).obj ((modulePullback B S hS a).obj M) ⟶
      (modulePullback B S hS f).obj ((modulePullback B S hS b).obj N)) :
    (modulePullback B S hS (f ≫ a)).obj M ⟶ (modulePullback B S hS (f ≫ b)).obj N :=
  comp₃ ((modulePullbackCompIso B S hS f a).inv.app M) ψ
    ((modulePullbackCompIso B S hS f b).hom.app N)

/-- `AlgebraicGeometry.Space.modulePullbackFlattenHom` as a composite. -/
theorem modulePullbackFlattenHom_eq (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ψ : (modulePullback B S hS f).obj ((modulePullback B S hS a).obj M) ⟶
      (modulePullback B S hS f).obj ((modulePullback B S hS b).obj N)) :
    modulePullbackFlattenHom f ψ = (modulePullbackCompIso B S hS f a).inv.app M ≫ ψ ≫
      (modulePullbackCompIso B S hS f b).hom.app N :=
  comp₃_eq ((modulePullbackCompIso B S hS f a).inv.app M) ψ
    ((modulePullbackCompIso B S hS f b).hom.app N)

/-- A morphism `(f ≫ a)^*ℳ ⟶ (f ≫ b)^*𝒩`, read through the comparisons of Stacks 03LU as a
morphism `f^*a^*ℳ ⟶ f^*b^*𝒩`. -/
def modulePullbackUnflattenHom (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (θ : (modulePullback B S hS (f ≫ a)).obj M ⟶ (modulePullback B S hS (f ≫ b)).obj N) :
    (modulePullback B S hS f).obj ((modulePullback B S hS a).obj M) ⟶
      (modulePullback B S hS f).obj ((modulePullback B S hS b).obj N) :=
  comp₃ ((modulePullbackCompIso B S hS f a).hom.app M) θ
    ((modulePullbackCompIso B S hS f b).inv.app N)

/-- Flattening is left inverse to unflattening. -/
theorem modulePullbackFlattenHom_unflattenHom (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (θ : (modulePullback B S hS (f ≫ a)).obj M ⟶ (modulePullback B S hS (f ≫ b)).obj N) :
    modulePullbackFlattenHom f (modulePullbackUnflattenHom f θ) = θ := by
  rw [modulePullbackFlattenHom_eq, modulePullbackUnflattenHom,
    comp₃_eq ((modulePullbackCompIso B S hS f a).hom.app M) θ
      ((modulePullbackCompIso B S hS f b).inv.app N)]
  simp only [Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **Flattening an inverse image of a morphism of inverse images** (Stacks 03LU): the
flattening of `g^*ψ`, read through `g ≫ p = v`, is the reindexing along `g` of the flattening of
`ψ`. -/
theorem modulePullbackFlattenHom_homTransport {A P T : AlgebraicSpaces B S hS} (a : A ⟶ Z)
    (b : A ⟶ Z') {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (g : T ⟶ P) (p : P ⟶ A) {v : T ⟶ A} (hv : g ≫ p = v)
    (ψ : (modulePullback B S hS p).obj ((modulePullback B S hS a).obj M) ⟶
      (modulePullback B S hS p).obj ((modulePullback B S hS b).obj N))
    (e₁ : v ≫ a = g ≫ p ≫ a) (e₂ : g ≫ p ≫ b = v ≫ b) :
    modulePullbackFlattenHom v (QuasiCoherentDescent.homTransport
        ((modulePullback B S hS a).obj M) ((modulePullback B S hS b).obj N) g hv ψ) =
      pullbackTransport M e₁ ≫ modulePullbackReindexHom g (modulePullbackFlattenHom p ψ) ≫
        pullbackTransport N e₂ := by
  subst hv
  have hassoc := modulePullbackCompIsoAssoc B S hS
  have key : modulePullbackFlattenHom (g ≫ p) (QuasiCoherentDescent.homTransport
        ((modulePullback B S hS a).obj M) ((modulePullback B S hS b).obj N) g rfl ψ) =
      modulePullbackReindexHom g (modulePullbackFlattenHom p ψ) := by
    rw [QuasiCoherentDescent.homTransport_def, QuasiCoherentDescent.homRebase_def,
      QuasiCoherentDescent.pullbackComparison_rfl, QuasiCoherentDescent.pullbackComparison_rfl,
      modulePullbackFlattenHom_eq,
      modulePullbackFlattenHom_eq, modulePullbackReindexHom_def]
    simp only [Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% (hassoc.inv_app g p a M), hassoc.hom_app g p b N]
  exact key.trans (id_comp_comp_id _)

/-- Reindexing along `f` is compatible with composition of morphisms. -/
theorem modulePullbackReindexHom_comp_morphism {Z'' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {a : Y ⟶ Z} {b : Y ⟶ Z'} {c : Y ⟶ Z''} {M : Modules.{u, u} B S hS Z.1 Z.2}
    {N : Modules.{u, u} B S hS Z'.1 Z'.2} {K : Modules.{u, u} B S hS Z''.1 Z''.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N)
    (β : (modulePullback B S hS b).obj N ⟶ (modulePullback B S hS c).obj K) :
    modulePullbackReindexHom f (α ≫ β) =
      modulePullbackReindexHom f α ≫ modulePullbackReindexHom f β := by
  simp [modulePullbackReindexHom, Category.assoc]

/-- The reindexings along `f` of the inverse and of the forward morphism of an isomorphism compose
to the identity. -/
theorem modulePullbackReindexHom_inv_hom (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ι : (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj N) :
    modulePullbackReindexHom f ι.inv ≫ modulePullbackReindexHom f ι.hom = 𝟙 _ := by
  simp [modulePullbackReindexHom, Category.assoc]

/-- The reindexings along `f` of the forward and of the inverse morphism of an isomorphism compose
to the identity. -/
theorem modulePullbackReindexHom_hom_inv (f : X ⟶ Y) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ι : (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj N) :
    modulePullbackReindexHom f ι.hom ≫ modulePullbackReindexHom f ι.inv = 𝟙 _ := by
  simp [modulePullbackReindexHom, Category.assoc]

/-- **Reindexing is functorial**, with the composite of the two reindexing morphisms given as
a separate morphism. -/
theorem modulePullbackReindexHom_comp' {W : AlgebraicSpaces B S hS} (w : W ⟶ X) (m : X ⟶ Y)
    (n : W ⟶ Y) (hn : w ≫ m = n) {a : Y ⟶ Z} {b : Y ⟶ Z'}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj N)
    (e₁ : w ≫ m ≫ a = n ≫ a) (e₂ : n ≫ b = w ≫ m ≫ b) :
    modulePullbackReindexHom w (modulePullbackReindexHom m α) =
      pullbackTransport M e₁ ≫ modulePullbackReindexHom n α ≫ pullbackTransport N e₂ := by
  subst hn
  have hassoc := modulePullbackCompIsoAssoc B S hS
  have hnat := (modulePullbackCompIso B S hS w m).hom.naturality α
  simp only [Functor.comp_map] at hnat
  have h₁ : modulePullbackReindexHom w (modulePullbackReindexHom m α) =
      modulePullbackReindexHom (w ≫ m) α := by
    simp only [modulePullbackReindexHom, Functor.map_comp, Category.assoc]
    rw [hassoc.hom_app w m b N, reassoc_of% hassoc.inv_app w m a M, reassoc_of% hnat]
    simp
  rw [h₁, pullbackTransport_eq_eqToHom, pullbackTransport_eq_eqToHom, eqToHom_refl,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The reindexing along `w` of the identification of the inverse images along `c = d` is the
identification of the inverse images along `w ≫ c = w ≫ d`. -/
theorem modulePullbackReindexHom_pullbackTransport (w : X ⟶ Y) {c d : Y ⟶ Z} (hcd : c = d)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (e : w ≫ c = w ≫ d) :
    modulePullbackReindexHom w (pullbackTransport M hcd) = pullbackTransport M e := by
  rw [modulePullbackReindexHom_eq]
  exact modulePullbackReindex_pullbackTransport w hcd M e

end ReindexHom

/-! ### The transported descent datum -/

/-- Two canonical identifications of inverse images compose to a third, followed by a
morphism. -/
theorem pullbackTransport_comp_assoc {T X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {f g h : T ⟶ X} (h₁ : f = g) (h₂ : g = h)
    (h₃ : f = h) {W : Modules.{u, u} B S hS T.1 T.2}
    (k : (modulePullback B S hS h).obj F ⟶ W) :
    pullbackTransport F h₁ ≫ pullbackTransport F h₂ ≫ k = pullbackTransport F h₃ ≫ k := by
  rw [← Category.assoc, pullbackTransport_comp F h₁ h₂ h₃]

/-- Two morphisms are equal if their conjugates by mutually inverse pairs are equal. -/
private theorem eq_of_comp_comp_eq_comp_comp {C : Type*} [Category C] {A A' D D' : C}
    {t₁ : A ⟶ A'} {s₁ : A' ⟶ A} {t₂ : D' ⟶ D} {s₂ : D ⟶ D'} (h₁ : s₁ ≫ t₁ = 𝟙 A')
    (h₂ : t₂ ≫ s₂ = 𝟙 D') {α β : A' ⟶ D'} (h : t₁ ≫ α ≫ t₂ = t₁ ≫ β ≫ t₂) : α = β :=
  (sandwich_cancel h₁ h₂ α).symm.trans
    ((congrArg (fun z => s₁ ≫ z ≫ s₂) h).trans (sandwich_cancel h₁ h₂ β))

section Transport

variable {U Y Z : AlgebraicSpaces B S hS} (π : U ⟶ Z) (u : U ⟶ Y)
  {M : Modules.{u, u} B S hS Z.1 Z.2} {G : Modules.{u, u} B S hS Y.1 Y.2}
  (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G)

/-- The canonical identification of the inverse images of `𝒢` along `x ≫ u = y ≫ u`, read
through `ι : π^*ℳ ≅ u^*𝒢` as a morphism `(x ≫ π)^*ℳ ⟶ (y ≫ π)^*ℳ`. -/
def descentTransportCore {P : AlgebraicSpaces B S hS} {x y : P ⟶ U} (h : x ≫ u = y ≫ u) :
    (modulePullback B S hS (x ≫ π)).obj M ⟶ (modulePullback B S hS (y ≫ π)).obj M :=
  comp₃ (modulePullbackReindexHom x ι.hom) (pullbackTransport G h)
    (modulePullbackReindexHom y ι.inv)

/-- `AlgebraicGeometry.Space.descentTransportCore`, read as a morphism `a^*ℳ ⟶ b^*ℳ` for
`a = x ≫ π`, `b = y ≫ π`. -/
def descentTransport {P : AlgebraicSpaces B S hS} {x y : P ⟶ U} {a b : P ⟶ Z}
    (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) :
    (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M :=
  comp₃ (pullbackTransport M ha.symm) (descentTransportCore π u ι h) (pullbackTransport M hb)

variable {π u}

/-- `AlgebraicGeometry.Space.descentTransportCore` as a composite. -/
theorem descentTransportCore_eq {P : AlgebraicSpaces B S hS} {x y : P ⟶ U}
    (h : x ≫ u = y ≫ u) :
    descentTransportCore π u ι h = modulePullbackReindexHom x ι.hom ≫ pullbackTransport G h ≫
      modulePullbackReindexHom y ι.inv :=
  comp₃_eq (modulePullbackReindexHom x ι.hom) (pullbackTransport G h)
    (modulePullbackReindexHom y ι.inv)

/-- `AlgebraicGeometry.Space.descentTransport` as a composite. -/
theorem descentTransport_eq {P : AlgebraicSpaces B S hS} {x y : P ⟶ U} {a b : P ⟶ Z}
    (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) :
    descentTransport π u ι ha hb h =
      pullbackTransport M ha.symm ≫ descentTransportCore π u ι h ≫ pullbackTransport M hb :=
  comp₃_eq (pullbackTransport M ha.symm) (descentTransportCore π u ι h) (pullbackTransport M hb)

/-- **The transported identifications compose.** -/
theorem descentTransportCore_comp {P : AlgebraicSpaces B S hS} {x y z : P ⟶ U}
    (h : x ≫ u = y ≫ u) (h' : y ≫ u = z ≫ u) (h'' : x ≫ u = z ≫ u) :
    descentTransportCore π u ι h ≫ descentTransportCore π u ι h' =
      descentTransportCore π u ι h'' := by
  rw [descentTransportCore_eq, descentTransportCore_eq, descentTransportCore_eq]
  simp only [Category.assoc]
  rw [reassoc_of% (modulePullbackReindexHom_inv_hom y ι), pullbackTransport_comp_assoc G h h' h'']

/-- The transported identifications `a^*ℳ ⟶ b^*ℳ` and `b^*ℳ ⟶ c^*ℳ` compose to the transported
identification `a^*ℳ ⟶ c^*ℳ`. -/
theorem descentTransport_comp {P : AlgebraicSpaces B S hS} {x y y' z : P ⟶ U} {a b c : P ⟶ Z}
    (ha : x ≫ π = a) (hb : y ≫ π = b) (hb' : y' ≫ π = b) (hc : z ≫ π = c)
    (h : x ≫ u = y ≫ u) (h' : y' ≫ u = z ≫ u) (hy : y = y') (h'' : x ≫ u = z ≫ u) :
    descentTransport π u ι ha hb h ≫ descentTransport π u ι hb' hc h' =
      descentTransport π u ι ha hc h'' := by
  subst hy
  rw [descentTransport_eq, descentTransport_eq, descentTransport_eq]
  simp only [Category.assoc]
  rw [← Category.assoc (pullbackTransport M hb) (pullbackTransport M hb'.symm),
    pullbackTransport_comp_self M hb hb'.symm, Category.id_comp,
    reassoc_of% (descentTransportCore_comp ι h h' h'')]

/-- **The transported identification on the diagonal is the identification of the two
composites.** -/
theorem descentTransportCore_self {P : AlgebraicSpaces B S hS} {x : P ⟶ U}
    (h : x ≫ u = x ≫ u) : descentTransportCore π u ι h = 𝟙 _ := by
  rw [descentTransportCore_eq, pullbackTransport_eq_eqToHom, eqToHom_refl, Category.id_comp,
    modulePullbackReindexHom_hom_inv]

/-- The transported identification on the diagonal is the identification of the inverse images
along `a = b`. -/
theorem descentTransport_self {P : AlgebraicSpaces B S hS} {x : P ⟶ U} {a b : P ⟶ Z}
    (ha : x ≫ π = a) (hb : x ≫ π = b) (h : x ≫ u = x ≫ u) (hab : a = b) :
    descentTransport π u ι ha hb h = pullbackTransport M hab := by
  rw [descentTransport_eq, descentTransportCore_self, Category.id_comp,
    pullbackTransport_comp M ha.symm hb hab]

/-- **The transported identifications are compatible with reindexing.** -/
theorem modulePullbackReindex_descentTransportCore {P P' : AlgebraicSpaces B S hS} (f : P' ⟶ P)
    {x y : P ⟶ U} (h : x ≫ u = y ≫ u) {x' y' : P' ⟶ U} (hx : f ≫ x = x') (hy : f ≫ y = y')
    (h' : x' ≫ u = y' ≫ u) (e₁ : f ≫ x ≫ π = x' ≫ π) (e₂ : y' ≫ π = f ≫ y ≫ π) :
    modulePullbackReindex f (descentTransportCore π u ι h) =
      pullbackTransport M e₁ ≫ descentTransportCore π u ι h' ≫ pullbackTransport M e₂ := by
  rw [← modulePullbackReindexHom_eq, descentTransportCore_eq,
    modulePullbackReindexHom_comp_morphism, modulePullbackReindexHom_comp_morphism,
    modulePullbackReindexHom_comp' f x x' hx ι.hom e₁ (by rw [← hx, Category.assoc]),
    modulePullbackReindexHom_comp' f y y' hy ι.inv (by rw [← hy, Category.assoc]) e₂,
    modulePullbackReindexHom_pullbackTransport _ h G
      (by rw [← Category.assoc, hx, ← Category.assoc, hy, h']),
    descentTransportCore_eq]
  simp only [Category.assoc]
  rw [pullbackTransport_comp_assoc G _ _ (by rw [h', ← hy, Category.assoc]),
    pullbackTransport_comp_assoc G _ _ h']

/-- **Identifications of inverse images are absorbed** into the transported identification. -/
theorem pullbackTransport_comp_descentTransport_comp {P : AlgebraicSpaces B S hS}
    {x y : P ⟶ U} {a b a' b' : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    (e₁ : a' = a) (e₂ : b = b') (ha' : x ≫ π = a') (hb' : y ≫ π = b') :
    pullbackTransport M e₁ ≫ descentTransport π u ι ha hb h ≫ pullbackTransport M e₂ =
      descentTransport π u ι ha' hb' h :=
  (congrArg (fun z => pullbackTransport M e₁ ≫ z ≫ pullbackTransport M e₂)
      (descentTransport_eq ι ha hb h)).trans <|
    (comp_transport_merge _ _ _ _ _ _ _ (pullbackTransport_comp M e₁ ha.symm ha'.symm)
      (pullbackTransport_comp M hb e₂ hb')).trans (descentTransport_eq ι ha' hb' h).symm

/-- An identification of inverse images on the left is absorbed into the transported
identification. -/
theorem pullbackTransport_comp_descentTransport {P : AlgebraicSpaces B S hS}
    {x y : P ⟶ U} {a b a' : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    (e₁ : a' = a) (ha' : x ≫ π = a') :
    pullbackTransport M e₁ ≫ descentTransport π u ι ha hb h =
      descentTransport π u ι ha' hb h :=
  (congrArg (pullbackTransport M e₁ ≫ ·) (Category.comp_id _)).symm.trans
    (pullbackTransport_comp_descentTransport_comp ι ha hb h e₁ rfl ha' hb)

/-- An identification of inverse images on the right is absorbed into the transported
identification. -/
theorem descentTransport_comp_pullbackTransport {P : AlgebraicSpaces B S hS}
    {x y : P ⟶ U} {a b b' : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    (e₂ : b = b') (hb' : y ≫ π = b') :
    descentTransport π u ι ha hb h ≫ pullbackTransport M e₂ =
      descentTransport π u ι ha hb' h :=
  (Category.id_comp _).symm.trans
    (pullbackTransport_comp_descentTransport_comp ι ha hb h rfl e₂ ha hb')

/-- The transported identification depends only on the two morphisms, not on how they are
written. -/
theorem descentTransport_congr {P : AlgebraicSpaces B S hS} {x y x' y' : P ⟶ U} {a b : P ⟶ Z}
    (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) (hx : x = x') (hy : y = y')
    (ha' : x' ≫ π = a) (hb' : y' ≫ π = b) (h' : x' ≫ u = y' ≫ u) :
    descentTransport π u ι ha hb h = descentTransport π u ι ha' hb' h' := by
  subst hx hy
  rfl

/-- **The transported identification between equal morphisms** is the identification of the
inverse images along equal morphisms. -/
theorem descentTransport_eq_pullbackTransport {P : AlgebraicSpaces B S hS} {x y : P ⟶ U}
    {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) (hxy : x = y)
    (hab : a = b) : descentTransport π u ι ha hb h = pullbackTransport M hab := by
  subst hxy
  exact descentTransport_self ι ha hb h hab

/-- **Reindexing the transported identification** along `f` is the transported identification
of the composed morphisms. -/
theorem modulePullbackReindex_descentTransport {P P' : AlgebraicSpaces B S hS} (f : P' ⟶ P)
    {x y : P ⟶ U} {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    {x' y' : P' ⟶ U} (hx : f ≫ x = x') (hy : f ≫ y = y') (ha' : x' ≫ π = f ≫ a)
    (hb' : y' ≫ π = f ≫ b) (h' : x' ≫ u = y' ≫ u) :
    modulePullbackReindex f (descentTransport π u ι ha hb h) =
      descentTransport π u ι ha' hb' h' := by
  have e₁ : f ≫ x ≫ π = x' ≫ π := by rw [← hx, Category.assoc]
  have e₂ : y' ≫ π = f ≫ y ≫ π := by rw [← hy, Category.assoc]
  have k₁ : f ≫ a = f ≫ x ≫ π := congrArg (f ≫ ·) ha.symm
  have k₂ : f ≫ y ≫ π = f ≫ b := congrArg (f ≫ ·) hb
  refine (congrArg (fun z => modulePullbackReindex f z) (descentTransport_eq ι ha hb h)).trans ?_
  refine (modulePullbackReindex_comp₃ B S hS f _ _ _).trans ?_
  refine (comp₃_congr (modulePullbackReindex_pullbackTransport f ha.symm M k₁)
    (modulePullbackReindex_descentTransportCore ι f h hx hy h' e₁ e₂)
    (modulePullbackReindex_pullbackTransport f hb M k₂)).trans ?_
  refine (comp_transport_merge _ _ _ _ _ _ _ (pullbackTransport_comp M k₁ e₁ ha'.symm)
    (pullbackTransport_comp M e₂ k₂ hb')).trans ?_
  exact (descentTransport_eq ι ha' hb' h').symm

/-- **Reindexing a morphism whose reindexing along `ρ` is a transported identification**:
along any morphism factoring through `ρ` it is again a transported identification. -/
theorem modulePullbackReindex_eq_descentTransport_of {V V' W : AlgebraicSpaces B S hS}
    {a b : V ⟶ Z} (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
    (ρ : V' ⟶ V) {x y : V' ⟶ U} (ha : x ≫ π = ρ ≫ a) (hb : y ≫ π = ρ ≫ b)
    (h : x ≫ u = y ≫ u) (hρ : modulePullbackReindex ρ α = descentTransport π u ι ha hb h)
    (f' : W ⟶ V') (f : W ⟶ V) (hf : f' ≫ ρ = f) {x' y' : W ⟶ U} (hx : f' ≫ x = x')
    (hy : f' ≫ y = y') (ha' : x' ≫ π = f ≫ a) (hb' : y' ≫ π = f ≫ b)
    (h' : x' ≫ u = y' ≫ u) :
    modulePullbackReindex f α = descentTransport π u ι ha' hb' h' := by
  have E₁ : f' ≫ ρ ≫ a = f ≫ a := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) hf)
  have E₂ : f ≫ b = f' ≫ ρ ≫ b := (congrArg (· ≫ b) hf).symm.trans (Category.assoc _ _ _)
  have ha'' : x' ≫ π = f' ≫ ρ ≫ a := ha'.trans E₁.symm
  have hb'' : y' ≫ π = f' ≫ ρ ≫ b := hb'.trans E₂
  have hc := modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) f' ρ f hf α E₁ E₂
  rw [hρ, modulePullbackReindex_descentTransport ι f' ha hb h hx hy ha'' hb'' h'] at hc
  exact eq_of_comp_comp_eq_comp_comp (pullbackTransport_comp_self M E₁.symm E₁)
    (pullbackTransport_comp_self M E₂ E₂.symm)
    (hc.symm.trans (pullbackTransport_comp_descentTransport_comp ι ha' hb' h' E₁ E₂ ha'' hb'').symm)

end Transport

/-! ### Isomorphic modules from equal transported descent data -/

section Comparison

/-- The inverse image of a morphism of inverse images is its reindexing, up to the
identifications of inverse images along `g ≫ p = v`. -/
theorem homTransport_eq_modulePullbackReindexHom {A P T : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (g : T ⟶ P) {p : P ⟶ A} {v : T ⟶ A}
    (hv : g ≫ p = v) (hv' : v = g ≫ p)
    (ψ : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS p).obj N) :
    QuasiCoherentDescent.homTransport M N g hv ψ =
      pullbackTransport M hv' ≫ modulePullbackReindexHom g ψ ≫ pullbackTransport N hv := by
  subst hv
  rw [QuasiCoherentDescent.homTransport_def, QuasiCoherentDescent.homRebase_def,
    QuasiCoherentDescent.pullbackComparison_rfl, QuasiCoherentDescent.pullbackComparison_rfl,
    modulePullbackReindexHom_def, pullbackTransport_eq_eqToHom, pullbackTransport_eq_eqToHom,
    eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- A conjugation identity in a category. -/
theorem comp_comp_eq_of_conj {C : Type*} [Category C] {X₁ X₂ A₁ A₂ B₁ B₂ : C}
    {i₁ : X₁ ⟶ A₁} {i₁' : A₁ ⟶ X₁} (hi : i₁' ≫ i₁ = 𝟙 A₁) (i₂ : X₁ ⟶ B₁) (p : A₁ ⟶ A₂)
    (q : B₁ ⟶ B₂) (j₁' : A₂ ⟶ X₂) {j₂' : B₂ ⟶ X₂} {j₂ : X₂ ⟶ B₂} (hj : j₂' ≫ j₂ = 𝟙 B₂)
    (h : i₁ ≫ p ≫ j₁' = i₂ ≫ q ≫ j₂') :
    (i₁' ≫ i₂) ≫ q = p ≫ j₁' ≫ j₂ := by
  calc (i₁' ≫ i₂) ≫ q = i₁' ≫ (i₂ ≫ q ≫ j₂') ≫ j₂ := by
        simp only [Category.assoc, hj, Category.comp_id]
    _ = p ≫ j₁' ≫ j₂ := by
        rw [← h]
        simp only [← Category.assoc, hi, Category.id_comp]

/-- Absorbing two morphisms into a commuting square. -/
theorem comp_eq_comp_of_comp_eq {P : AlgebraicSpaces B S hS}
    {X Y X' Y' : Modules.{u, u} B S hS P.1 P.2} {e₀ : X ⟶ X}
    {f₀ : Y ⟶ Y} {x : X ⟶ Y} {p : X ⟶ X'} {y : X' ⟶ Y'} {q : Y ⟶ Y'} {q' : Y' ⟶ Y}
    (he : e₀ ≫ p = p) (hf : q ≫ q' = f₀) (h : x ≫ q = p ≫ y) :
    e₀ ≫ x ≫ f₀ = p ≫ y ≫ q' := by
  rw [← hf, ← Category.assoc x, h, Category.assoc, ← Category.assoc, he]

/-- **The condition of Stacks 04W5 from its flattened form**: a morphism `ψ : u^*M ⟶ u^*N`
is compatible with the canonical comparisons at `a`, `b` once its reindexings along `a` and `b`
are intertwined by the identifications of inverse images along `a ≫ u = b ≫ u`. -/
theorem map_comp_canonicalComparison_of_reindexHom {A U P : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (u : U ⟶ A) (a b : P ⟶ U) (hab : a ≫ u = b ≫ u)
    (ψ : (modulePullback B S hS u).obj M ⟶ (modulePullback B S hS u).obj N)
    (h : modulePullbackReindexHom a ψ ≫ pullbackTransport N hab =
      pullbackTransport M hab ≫ modulePullbackReindexHom b ψ) :
    (modulePullback B S hS a).map ψ ≫ (QuasiCoherentDescent.canonicalComparison a b u u hab N).hom =
      (QuasiCoherentDescent.canonicalComparison a b u u hab M).hom ≫
        (modulePullback B S hS b).map ψ :=
  (QuasiCoherentDescent.map_comp_canonicalComparison_iff a b u hab ψ).2
    ((homTransport_eq_modulePullbackReindexHom a rfl rfl ψ).trans
      ((comp_eq_comp_of_comp_eq (pullbackTransport_comp M rfl hab hab)
        (pullbackTransport_comp N hab hab.symm rfl) h).trans
        (homTransport_eq_modulePullbackReindexHom b hab.symm hab ψ).symm))

/-- **Two transported descent data that agree at every pair** give a morphism of the modules on
the base: `ι₁⁻¹ ≫ ι₂` descends along the étale covering `u` (Stacks 04W6). -/
theorem exists_modulePullback_map_eq_of_descentTransportCore_eq {U Y Z : AlgebraicSpaces B S hS}
    (u : U ⟶ Y) (hu : IsEtale B S hS u.hom) (hrep : yoneda.relativelyRepresentable u.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => U.1) (fun _ => u.hom)) (ρ : U ⟶ Z)
    {M : Modules.{u, u} B S hS Z.1 Z.2} {A G : Modules.{u, u} B S hS Y.1 Y.2}
    (ι₁ : (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS u).obj A)
    (ι₂ : (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS u).obj G)
    (h : ∀ (P : AlgebraicSpaces B S hS) (a b : P ⟶ U) (hab : a ≫ u = b ≫ u),
      descentTransportCore ρ u ι₁ hab = descentTransportCore ρ u ι₂ hab) :
    ∃ χ : A ⟶ G, (modulePullback B S hS u).map χ = ι₁.inv ≫ ι₂.hom :=
  QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated B S hS u hu hrep hcov _
    fun P a b hab => map_comp_canonicalComparison_of_reindexHom u a b hab _
      ((modulePullbackReindexHom_comp_morphism a ι₁.inv ι₂.hom).symm ▸
        (modulePullbackReindexHom_comp_morphism b ι₁.inv ι₂.hom).symm ▸
        comp_comp_eq_of_conj (modulePullbackReindexHom_inv_hom a ι₁) _ _ _ _
          (modulePullbackReindexHom_inv_hom b ι₂)
          ((descentTransportCore_eq ι₁ hab).symm.trans
            ((h P a b hab).trans (descentTransportCore_eq ι₂ hab))))

/-- **Two transported descent data that agree at the kernel pair of the étale covering `u`**
identify the two modules on the base (Stacks 04W6, 04W5). -/
theorem nonempty_iso_of_descentTransportCore_eq {U Y Z R : AlgebraicSpaces B S hS}
    (u : U ⟶ Y) (hu : IsEtale B S hS u.hom) (hrep : yoneda.relativelyRepresentable u.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => U.1) (fun _ => u.hom)) {t s : R ⟶ U}
    (hk : IsPullback t.hom s.hom u.hom u.hom) (ρ : U ⟶ Z) {M : Modules.{u, u} B S hS Z.1 Z.2}
    {A G : Modules.{u, u} B S hS Y.1 Y.2}
    (ι₁ : (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS u).obj A)
    (ι₂ : (modulePullback B S hS ρ).obj M ≅ (modulePullback B S hS u).obj G)
    (hts : t ≫ u = s ≫ u)
    (h : descentTransportCore ρ u ι₁ hts = descentTransportCore ρ u ι₂ hts) :
    Nonempty (A ≅ G) := by
  have hall : ∀ (P : AlgebraicSpaces B S hS) (a b : P ⟶ U) (hab : a ≫ u = b ≫ u),
      descentTransportCore ρ u ι₁ hab = descentTransportCore ρ u ι₂ hab := by
    intro P a b hab
    obtain ⟨v, hva, hvb⟩ : ∃ v : P ⟶ R, v ≫ t = a ∧ v ≫ s = b :=
      ⟨ObjectProperty.homMk (hk.lift a.hom b.hom (congrArg (fun f => f.hom) hab)),
        ObjectProperty.hom_ext _ (hk.lift_fst _ _ _), ObjectProperty.hom_ext _ (hk.lift_snd _ _ _)⟩
    have e₁ : v ≫ t ≫ ρ = a ≫ ρ := by rw [← hva, Category.assoc]
    have e₂ : b ≫ ρ = v ≫ s ≫ ρ := by rw [← hvb, Category.assoc]
    have h₁ := modulePullbackReindex_descentTransportCore ι₁ v hts hva hvb hab e₁ e₂
    have h₂ := modulePullbackReindex_descentTransportCore ι₂ v hts hva hvb hab e₁ e₂
    rw [h] at h₁
    exact eq_of_comp_comp_eq_comp_comp (pullbackTransport_comp_self M e₁.symm e₁)
      (pullbackTransport_comp_self M e₂ e₂.symm) (h₁.symm.trans h₂)
  obtain ⟨χ, hχ⟩ := exists_modulePullback_map_eq_of_descentTransportCore_eq u hu hrep hcov ρ ι₁ ι₂
    hall
  obtain ⟨χ', hχ'⟩ := exists_modulePullback_map_eq_of_descentTransportCore_eq u hu hrep hcov ρ ι₂
    ι₁ fun P a b hab => (hall P a b hab).symm
  have hinj := fun {N N' : Modules.{u, u} B S hS Y.1 Y.2} (f g : N ⟶ N')
      (hfg : (modulePullback B S hS u).map f = (modulePullback B S hS u).map g) =>
    QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
      (fun _ : Unit => U) (fun _ => u) hcov f g fun _ => hfg
  refine ⟨{ hom := χ, inv := χ', hom_inv_id := hinj _ _ ?_, inv_hom_id := hinj _ _ ?_ }⟩ <;>
    rw [CategoryTheory.Functor.map_comp, hχ, hχ', CategoryTheory.Functor.map_id] <;> simp

end Comparison

/-! ### Changing the morphisms along which the descent datum is transported -/

section Change

/-- The reindexing along `f` of an isomorphism `a^*ℳ ≅ b^*𝒩`. -/
def modulePullbackReindexIso {X Y Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y) {a : Y ⟶ Z}
    {b : Y ⟶ Z'} {M : Modules.{u, u} B S hS Z.1 Z.2} {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ι : (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj N) :
    (modulePullback B S hS (f ≫ a)).obj M ≅ (modulePullback B S hS (f ≫ b)).obj N where
  hom := modulePullbackReindexHom f ι.hom
  inv := modulePullbackReindexHom f ι.inv
  hom_inv_id := modulePullbackReindexHom_hom_inv f ι
  inv_hom_id := modulePullbackReindexHom_inv_hom f ι

/-- The forward morphism of the reindexing of `ι` is the reindexing of the forward morphism of
`ι`. -/
theorem modulePullbackReindexIso_hom {X Y Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {a : Y ⟶ Z} {b : Y ⟶ Z'} {M : Modules.{u, u} B S hS Z.1 Z.2}
    {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ι : (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj N) :
    (modulePullbackReindexIso f ι).hom = modulePullbackReindexHom f ι.hom :=
  rfl

/-- The inverse of the reindexing of `ι` is the reindexing of the inverse of `ι`. -/
theorem modulePullbackReindexIso_inv {X Y Z Z' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {a : Y ⟶ Z} {b : Y ⟶ Z'} {M : Modules.{u, u} B S hS Z.1 Z.2}
    {N : Modules.{u, u} B S hS Z'.1 Z'.2}
    (ι : (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj N) :
    (modulePullbackReindexIso f ι).inv = modulePullbackReindexHom f ι.inv :=
  rfl

/-- Merging the transports around two sandwiched morphisms. -/
theorem comp_sandwich_merge {C : Type*} [Category C]
    {A₀ A₁ A₂ B₁ B₂ B₃ B₄ D₁ D₂ D₃ : C} (t₁ : A₀ ⟶ A₁) (t₂ : A₁ ⟶ A₂) (x : A₂ ⟶ B₁)
    (t₃ : B₁ ⟶ B₂) (t₄ : B₂ ⟶ B₃) (t₅ : B₃ ⟶ B₄) (y : B₄ ⟶ D₁) (t₆ : D₁ ⟶ D₂) (t₇ : D₂ ⟶ D₃)
    (k₁ : A₀ ⟶ A₂) (k₂ : B₁ ⟶ B₄) (k₃ : D₁ ⟶ D₃) (h₁ : t₁ ≫ t₂ = k₁)
    (h₂ : t₃ ≫ t₄ ≫ t₅ = k₂) (h₃ : t₆ ≫ t₇ = k₃) :
    t₁ ≫ ((t₂ ≫ x ≫ t₃) ≫ t₄ ≫ (t₅ ≫ y ≫ t₆)) ≫ t₇ = k₁ ≫ (x ≫ k₂ ≫ y) ≫ k₃ := by
  rw [← h₁, ← h₂, ← h₃]
  simp only [Category.assoc]

/-- Reassociating a row of five morphisms. -/
theorem comp_assoc_five {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) :
    f₁ ≫ (f₂ ≫ f₃ ≫ f₄) ≫ f₅ = (f₁ ≫ f₂) ≫ f₃ ≫ f₄ ≫ f₅ := by
  simp only [Category.assoc]

/-- Merging three middle factors of a row. -/
theorem comp_merge_three {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (r : A₀ ⟶ A₁)
    (t₁ : A₁ ⟶ A₂) (q : A₂ ⟶ A₃) (t₂ : A₃ ⟶ A₄) (r' : A₄ ⟶ A₅) (m : A₁ ⟶ A₄)
    (hm : t₁ ≫ q ≫ t₂ = m) : (r ≫ t₁) ≫ q ≫ t₂ ≫ r' = r ≫ m ≫ r' := by
  rw [← hm]
  simp only [Category.assoc]

/-- Merging the outer transports of a sandwich. -/
theorem comp_sandwich_merge' {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (t₁ : A₀ ⟶ A₁)
    (t₂ : A₁ ⟶ A₂) (x : A₂ ⟶ A₃) (t₃ : A₃ ⟶ A₄) (t₄ : A₄ ⟶ A₅) (k₁ : A₀ ⟶ A₂) (k₂ : A₃ ⟶ A₅)
    (h₁ : t₁ ≫ t₂ = k₁) (h₂ : t₃ ≫ t₄ = k₂) :
    t₁ ≫ (t₂ ≫ x ≫ t₃) ≫ t₄ = k₁ ≫ x ≫ k₂ := by
  rw [← h₁, ← h₂]
  simp only [Category.assoc]

/-- Merging a row of morphisms in two steps. -/
theorem comp_comp_merge {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    (r : A₀ ⟶ A₁) (t₁ : A₁ ⟶ A₂) (c₁ : A₂ ⟶ A₃) (q : A₃ ⟶ A₄) (c₂ : A₄ ⟶ A₅) (t₂ : A₅ ⟶ A₆)
    (r' : A₆ ⟶ A₇) (k : A₂ ⟶ A₅) (hk : c₁ ≫ q ≫ c₂ = k) (m : A₁ ⟶ A₆)
    (hm : t₁ ≫ k ≫ t₂ = m) :
    (r ≫ t₁ ≫ c₁) ≫ q ≫ (c₂ ≫ t₂) ≫ r' = r ≫ m ≫ r' := by
  rw [← hm, ← hk]
  simp only [Category.assoc]

variable {U Y Z : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS Z.1 Z.2}
  {G : Modules.{u, u} B S hS Y.1 Y.2}

/-- **The transported descent datum along morphisms factoring through `g`** is the descent datum
transported through the reindexing of `ι` along `g`. -/
theorem descentTransport_comp_left {U' P : AlgebraicSpaces B S hS} (π : U ⟶ Z) (u : U ⟶ Y)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) (g : U' ⟶ U)
    {x₁ y₁ : P ⟶ U'} {x y : P ⟶ U} (hx : x₁ ≫ g = x) (hy : y₁ ≫ g = y) {a b : P ⟶ Z}
    (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) (ha' : x₁ ≫ g ≫ π = a)
    (hb' : y₁ ≫ g ≫ π = b) (h' : x₁ ≫ g ≫ u = y₁ ≫ g ≫ u) :
    descentTransport π u ι ha hb h =
      descentTransport (g ≫ π) (g ≫ u) (modulePullbackReindexIso g ι) ha' hb' h' := by
  subst hx hy
  have e₁ : x₁ ≫ g ≫ π = (x₁ ≫ g) ≫ π := (Category.assoc _ _ _).symm
  have e₂ : (x₁ ≫ g) ≫ u = x₁ ≫ g ≫ u := Category.assoc _ _ _
  have e₃ : y₁ ≫ g ≫ u = (y₁ ≫ g) ≫ u := (Category.assoc _ _ _).symm
  have e₄ : (y₁ ≫ g) ≫ π = y₁ ≫ g ≫ π := Category.assoc _ _ _
  refine (descentTransport_eq ι ha hb h).trans ?_
  refine Eq.trans ?_ (descentTransport_eq (modulePullbackReindexIso g ι) ha' hb' h').symm
  refine Eq.trans ?_ (congrArg (fun z => pullbackTransport M ha'.symm ≫ z ≫
    pullbackTransport M hb') (descentTransportCore_eq (modulePullbackReindexIso g ι) h')).symm
  rw [modulePullbackReindexIso_hom, modulePullbackReindexIso_inv,
    modulePullbackReindexHom_comp' x₁ g (x₁ ≫ g) rfl ι.hom e₁ e₂,
    modulePullbackReindexHom_comp' y₁ g (y₁ ≫ g) rfl ι.inv e₃ e₄,
    comp_sandwich_merge _ _ _ _ _ _ _ _ _ _ _ _ (pullbackTransport_comp M ha'.symm e₁ ha.symm)
      (pullbackTransport_comp₃ B S hS G e₂ h' e₃ h) (pullbackTransport_comp M e₄ hb' hb),
    descentTransportCore_eq]

/-- Reindexing a comparison of Stacks 03LU along `x` is a comparison of Stacks 03LU, read
through `x ≫ u' ≫ p = (x ≫ u') ≫ p`. -/
theorem modulePullbackReindexHom_pullbackComparison_hom {U' Y' P : AlgebraicSpaces B S hS}
    (u' : U' ⟶ Y') (p : Y' ⟶ Y) (x : P ⟶ U') (e : x ≫ u' ≫ p = (x ≫ u') ≫ p) :
    modulePullbackReindexHom x (QuasiCoherentDescent.pullbackComparison B S hS u' p (u' ≫ p) rfl
      G).hom = pullbackTransport G e ≫
        (QuasiCoherentDescent.pullbackComparison B S hS (x ≫ u') p ((x ≫ u') ≫ p) rfl G).hom := by
  rw [QuasiCoherentDescent.pullbackComparison_rfl, QuasiCoherentDescent.pullbackComparison_rfl,
    modulePullbackReindexHom_def, pullbackTransport_eq_eqToHom, eqToHom_refl, Category.id_comp]
  simp only [Iso.symm_hom, Iso.app_inv]
  rw [reassoc_of% ((modulePullbackCompIsoAssoc B S hS).inv_app x u' p G), Iso.inv_hom_id_app,
    Category.comp_id]

/-- Reindexing the inverse of a comparison of Stacks 03LU along `x` is the inverse of a comparison
of Stacks 03LU, read through `(x ≫ u') ≫ p = x ≫ u' ≫ p`. -/
theorem modulePullbackReindexHom_pullbackComparison_inv {U' Y' P : AlgebraicSpaces B S hS}
    (u' : U' ⟶ Y') (p : Y' ⟶ Y) (x : P ⟶ U') (e : (x ≫ u') ≫ p = x ≫ u' ≫ p) :
    modulePullbackReindexHom x (QuasiCoherentDescent.pullbackComparison B S hS u' p (u' ≫ p) rfl
      G).inv = (QuasiCoherentDescent.pullbackComparison B S hS (x ≫ u') p ((x ≫ u') ≫ p) rfl
        G).inv ≫ pullbackTransport G e := by
  rw [QuasiCoherentDescent.pullbackComparison_rfl, QuasiCoherentDescent.pullbackComparison_rfl,
    modulePullbackReindexHom_def, pullbackTransport_eq_eqToHom, eqToHom_refl, Category.comp_id]
  simp only [Iso.symm_inv, Iso.app_hom]
  rw [(modulePullbackCompIsoAssoc B S hS).hom_app x u' p G, Iso.inv_hom_id_app_assoc]

/-- The identification of the inverse images of `p^*𝒢` along `c = d`, read through the
comparisons of Stacks 03LU, is the identification of the inverse images of `𝒢`. -/
theorem pullbackComparison_hom_comp_pullbackTransport {Y' P : AlgebraicSpaces B S hS}
    (p : Y' ⟶ Y) {c d : P ⟶ Y'} (h : c = d) (e : c ≫ p = d ≫ p) :
    (QuasiCoherentDescent.pullbackComparison B S hS c p (c ≫ p) rfl G).hom ≫
        pullbackTransport ((modulePullback B S hS p).obj G) h ≫
          (QuasiCoherentDescent.pullbackComparison B S hS d p (d ≫ p) rfl G).inv =
      pullbackTransport G e := by
  subst h
  rw [pullbackTransport_eq_eqToHom, pullbackTransport_eq_eqToHom, eqToHom_refl, eqToHom_refl,
    Category.id_comp, Iso.hom_inv_id]

/-- **The transported descent datum along a composite `u' ≫ p`** is the descent datum of `p^*𝒢`
along `u'`, transported through the comparison of Stacks 03LU. -/
theorem descentTransportCore_comp_right {Y' P : AlgebraicSpaces B S hS} (π : U ⟶ Z)
    (u' : U ⟶ Y') (p : Y' ⟶ Y)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS (u' ≫ p)).obj G)
    {x y : P ⟶ U} (h : x ≫ u' ≫ p = y ≫ u' ≫ p) (h' : x ≫ u' = y ≫ u')
    (e : (x ≫ u') ≫ p = (y ≫ u') ≫ p) (ex : x ≫ u' ≫ p = (x ≫ u') ≫ p)
    (ey : (y ≫ u') ≫ p = y ≫ u' ≫ p) :
    descentTransportCore π (u' ≫ p) ι h = descentTransportCore π u'
      (ι ≪≫ QuasiCoherentDescent.pullbackComparison B S hS u' p (u' ≫ p) rfl G) h' := by
  refine Eq.symm ((descentTransportCore_eq _ h').trans ?_)
  refine Eq.trans ?_ (descentTransportCore_eq ι h).symm
  rw [Iso.trans_hom, Iso.trans_inv, modulePullbackReindexHom_comp_morphism,
    modulePullbackReindexHom_comp_morphism,
    modulePullbackReindexHom_pullbackComparison_hom u' p x ex,
    modulePullbackReindexHom_pullbackComparison_inv u' p y ey]
  exact comp_comp_merge _ _ _ _ _ _ _ _ (pullbackComparison_hom_comp_pullbackTransport p h' e) _
    (pullbackTransport_comp₃ B S hS G ex e ey h)

/-- The identification of the inverse images along two equal morphisms, as an isomorphism. -/
def pullbackTransportIso {T X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    {f g : T ⟶ X} (h : f = g) :
    (modulePullback B S hS f).obj M ≅ (modulePullback B S hS g).obj M :=
  eqToIso (congrArg (fun k : T ⟶ X => (modulePullback B S hS k).obj M) h)

/-- The forward morphism of `AlgebraicGeometry.Space.pullbackTransportIso` is the identification of
the inverse images along `f = g`. -/
theorem pullbackTransportIso_hom {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) :
    (pullbackTransportIso M h).hom = pullbackTransport M h :=
  rfl

/-- The inverse of `AlgebraicGeometry.Space.pullbackTransportIso` is the identification of the
inverse images along `g = f`. -/
theorem pullbackTransportIso_inv {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g : T ⟶ X} (h : f = g) (h' : g = f) :
    (pullbackTransportIso M h).inv = pullbackTransport M h' :=
  rfl

/-- **Changing the morphism to the base along an equality.** -/
theorem descentTransportCore_congr_right {P : AlgebraicSpaces B S hS} (π : U ⟶ Z) {u u' : U ⟶ Y}
    (hu : u = u') (hu' : u' = u)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {x y : P ⟶ U}
    (h : x ≫ u = y ≫ u) (h' : x ≫ u' = y ≫ u') (ex : x ≫ u = x ≫ u') (ey : y ≫ u' = y ≫ u) :
    descentTransportCore π u ι h =
      descentTransportCore π u' (ι ≪≫ pullbackTransportIso G hu) h' := by
  refine Eq.trans ?_ (descentTransportCore_eq _ h').symm
  rw [descentTransportCore_eq, Iso.trans_hom, Iso.trans_inv, pullbackTransportIso_hom,
    pullbackTransportIso_inv G hu hu', modulePullbackReindexHom_comp_morphism,
    modulePullbackReindexHom_comp_morphism, modulePullbackReindexHom_pullbackTransport x hu G ex,
    modulePullbackReindexHom_pullbackTransport y hu' G ey]
  exact (comp_merge_three _ _ _ _ _ _ (pullbackTransport_comp₃ B S hS G ex h' ey h)).symm

/-- **Changing the morphism to `Z` along an equality.** -/
theorem descentTransportCore_congr_left {P : AlgebraicSpaces B S hS} {π π' : U ⟶ Z} (u : U ⟶ Y)
    (hπ : π = π') (hπ' : π' = π)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {x y : P ⟶ U}
    (h : x ≫ u = y ≫ u) (ex : x ≫ π' = x ≫ π) (ey : y ≫ π = y ≫ π') :
    pullbackTransport M ex ≫ descentTransportCore π u ι h ≫ pullbackTransport M ey =
      descentTransportCore π' u (pullbackTransportIso M hπ' ≪≫ ι) h := by
  refine Eq.trans ?_ (descentTransportCore_eq _ h).symm
  rw [descentTransportCore_eq, Iso.trans_hom, Iso.trans_inv, pullbackTransportIso_hom,
    pullbackTransportIso_inv M hπ' hπ, modulePullbackReindexHom_comp_morphism,
    modulePullbackReindexHom_comp_morphism, modulePullbackReindexHom_pullbackTransport x hπ' M ex,
    modulePullbackReindexHom_pullbackTransport y hπ M ey]
  exact comp_assoc_five _ _ _ _ _

/-- **Changing the morphism to `Z` along an equality**, for the transported identifications
between inverse images along fixed morphisms `a`, `b`. -/
theorem descentTransport_congr_left {P : AlgebraicSpaces B S hS} {π π' : U ⟶ Z} (u : U ⟶ Y)
    (hπ : π = π') (hπ' : π' = π)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {x y : P ⟶ U}
    {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u) (ha' : x ≫ π' = a)
    (hb' : y ≫ π' = b) (ex : x ≫ π' = x ≫ π) (ey : y ≫ π = y ≫ π') :
    descentTransport π u ι ha hb h =
      descentTransport π' u (pullbackTransportIso M hπ' ≪≫ ι) ha' hb' h := by
  rw [descentTransport_eq, descentTransport_eq,
    ← descentTransportCore_congr_left u hπ hπ' ι h ex ey]
  exact (comp_sandwich_merge' _ _ _ _ _ _ _ (pullbackTransport_comp M ha'.symm ex ha.symm)
    (pullbackTransport_comp M ey hb' hb)).symm

/-- **Changing the morphism to the base along an equality**, for the transported identifications
between inverse images along fixed morphisms `a`, `b`. -/
theorem descentTransport_congr_right {P : AlgebraicSpaces B S hS} (π : U ⟶ Z) {u u' : U ⟶ Y}
    (hu : u = u') (hu' : u' = u)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {x y : P ⟶ U}
    {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    (h' : x ≫ u' = y ≫ u') (ex : x ≫ u = x ≫ u') (ey : y ≫ u' = y ≫ u) :
    descentTransport π u ι ha hb h =
      descentTransport π u' (ι ≪≫ pullbackTransportIso G hu) ha hb h' := by
  rw [descentTransport_eq, descentTransport_eq,
    descentTransportCore_congr_right π hu hu' ι h h' ex ey]

/-- **The transported identification along a composite `u' ≫ p`**, for the transported
identifications between inverse images along fixed morphisms `a`, `b`. -/
theorem descentTransport_comp_right {Y' P : AlgebraicSpaces B S hS} (π : U ⟶ Z)
    (u' : U ⟶ Y') (p : Y' ⟶ Y)
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS (u' ≫ p)).obj G)
    {x y : P ⟶ U} {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b)
    (h : x ≫ u' ≫ p = y ≫ u' ≫ p) (h' : x ≫ u' = y ≫ u')
    (e : (x ≫ u') ≫ p = (y ≫ u') ≫ p) (ex : x ≫ u' ≫ p = (x ≫ u') ≫ p)
    (ey : (y ≫ u') ≫ p = y ≫ u' ≫ p) :
    descentTransport π (u' ≫ p) ι ha hb h = descentTransport π u'
      (ι ≪≫ QuasiCoherentDescent.pullbackComparison B S hS u' p (u' ≫ p) rfl G) ha hb h' := by
  rw [descentTransport_eq, descentTransport_eq,
    descentTransportCore_comp_right π u' p ι h h' e ex ey]

/-- Equal transported identifications have equal cores. -/
theorem descentTransportCore_eq_of_descentTransport_eq {P : AlgebraicSpaces B S hS}
    (π : U ⟶ Z) (u : U ⟶ Y) {G' : Modules.{u, u} B S hS Y.1 Y.2}
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G)
    (ι' : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G')
    {x y : P ⟶ U} {a b : P ⟶ Z} (ha : x ≫ π = a) (hb : y ≫ π = b) (h : x ≫ u = y ≫ u)
    (heq : descentTransport π u ι ha hb h = descentTransport π u ι' ha hb h) :
    descentTransportCore π u ι h = descentTransportCore π u ι' h := by
  rw [descentTransport_eq, descentTransport_eq] at heq
  exact eq_of_comp_comp_eq_comp_comp (pullbackTransport_comp_self M ha ha.symm)
    (pullbackTransport_comp_self M hb hb.symm) heq

end Change

end AlgebraicGeometry.Space

end
