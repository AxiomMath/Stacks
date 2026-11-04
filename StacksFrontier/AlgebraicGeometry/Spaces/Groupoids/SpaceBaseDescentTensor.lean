module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp

/-!
# The canonical transition morphism of an inverse image is monoidal

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`.  The
inverse image of `𝒪`-modules of Stacks 03LU carries tensor products to tensor products
(`AlgebraicGeometry.Space.modulePullbackTensorIso`, Stacks 03EL), and the comparison
`f^*g^* ≅ (f ≫ g)^*` of iterated inverse images (`AlgebraicGeometry.Space.modulePullbackCompIso`)
is compatible with it: this is the composition law of Stacks 03EL for morphisms of algebraic
spaces.  As a consequence, the canonical transition morphism `t^*φ^*Y ⟶ s^*φ^*Y` of a module
pulled back to the object space of a groupoid (`AlgebraicGeometry.Space.spaceBaseDescent`,
the descent datum of Stacks 03M3) is compatible with tensor products.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_tensor`: **the composition law of
  Stacks 03EL for morphisms of algebraic spaces**,
  `c(F ⊗ G) ≫ PTI_{f ≫ g} = f^*PTI_g ≫ PTI_f ≫ (c F ⊗ c G)`.
* `AlgebraicGeometry.Space.modulePullbackUnflatten_pullbackTransport_tensor`: unflattening the
  transport along `a ≫ φ = b ≫ φ` is compatible with tensor products.
* `AlgebraicGeometry.Space.spaceBaseDescent_tensor`: **the canonical transition morphism of an
  inverse image to a groupoid is compatible with tensor products.**

## Implementation notes

The composition law is the four-field law
`Stacks.SheafOfModules.pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app` read through
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_eq`.  Its statement is spelled with the inverse
image of modules of the four-field morphism of small étale ringed topoi and with the tensor
product sheaf of the structure ring of the small étale ringed topos, while the statement here is
spelled with `AlgebraicGeometry.Space.modulePullback` and the structure sheaf of the algebraic
space.  The two spellings are definitionally equal argument by argument, but when the unifier
meets a projection such as `CategoryTheory.NatTrans.app` applied to the image of a morphism under
`Stacks.SheafOfModules.Tensor.sheafTensor` it tries to reduce that image to a constructor, which
unfolds sheafification and exhausts the recursion depth.  The tensor product sheaf, the
comparison of Stacks 03EL and the comparison of pullbacks are therefore made locally irreducible
for the proof of the composition law, so that the two spellings are compared argument by
argument; the computation itself is the abstract lemma `comp_tensor_of_readings`, instantiated
once.  Downstream, the comparisons of iterated inverse images are typed with the iterated
inverse image spelled out (`AlgebraicGeometry.Space.modulePullbackCompHom`,
`AlgebraicGeometry.Space.modulePullbackCompInv`), so that the kernel never compares
`(g^* ⋙ f^*).obj M` with `f^*.obj (g^*.obj M)` inside a larger term.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-- The abstract shape of `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_tensor`, at
variables. -/
private theorem comp_tensor_of_readings {CZ CY CX : Type*} [Category CZ] [Category CY] [Category CX]
    (Pg : CZ ⥤ CY) (Pf : CY ⥤ CX) (Pfg : CZ ⥤ CX) (c c' : Pg ⋙ Pf ⟶ Pfg) (hcc : c = c')
    {a s : CZ} (eZ : a ≅ s) {b s' : CY} (eY : b ≅ s') (Tg : Pg.obj s ≅ s')
    {x x₀ y y₀ : CX} (eX' : x ≅ x₀) (Tf : Pf.obj s' ≅ x₀) (eX : y ≅ y₀) (T : Pfg.obj s ≅ y₀)
    (q q' : x ⟶ y) (hq : q = q') (w : x₀ ⟶ y₀)
    (K : c'.app s ≫ T.hom = Pf.map Tg.hom ≫ Tf.hom ≫ w)
    (nm : q' ≫ eX.hom = eX'.hom ≫ w) :
    c.app a ≫ (Pfg.mapIso eZ ≪≫ T ≪≫ eX.symm).hom =
      Pf.map (Pg.mapIso eZ ≪≫ Tg ≪≫ eY.symm).hom ≫ (Pf.mapIso eY ≪≫ Tf ≪≫ eX'.symm).hom ≫ q := by
  subst hcc hq
  have nm' : eX'.inv ≫ q = w ≫ eX.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, nm, Iso.inv_hom_id_assoc]
  have hc : c.app a ≫ Pfg.map eZ.hom = Pf.map (Pg.map eZ.hom) ≫ c.app s :=
    (c.naturality eZ.hom).symm
  have e1 : Pf.map (Pg.map eZ.hom ≫ Tg.hom ≫ eY.inv) ≫ Pf.map eY.hom =
      Pf.map (Pg.map eZ.hom) ≫ Pf.map Tg.hom := by
    rw [← Pf.map_comp, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Pf.map_comp]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% e1, nm', reassoc_of% hc, reassoc_of% K]

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.SheafOfModules.pullbackTensorIso Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition law of Stacks 03EL for morphisms of algebraic spaces.**  For
`f : X ⟶ Y`, `g : Y ⟶ Z` and `𝒪_Z`-modules `F`, `G`, the comparison
`f^*g^*(F ⊗ G) ⟶ (f ≫ g)^*(F ⊗ G)` of Stacks 03LU followed by the monoidality of `(f ≫ g)^*` is
the inverse image along `f` of the monoidality of `g^*`, followed by the monoidality of `f^*` and
the comparisons of Stacks 03LU in both factors. -/
theorem modulePullbackCompIso_hom_app_tensor (f : X ⟶ Y) (g : Y ⟶ Z)
    (F G : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackCompIso B S hS f g).hom.app (F ⊗ G) ≫
        (modulePullbackTensorIso B S hS (f ≫ g) F G).hom =
      (modulePullback B S hS f).map (modulePullbackTensorIso B S hS g F G).hom ≫
        (modulePullbackTensorIso B S hS f _ _).hom ≫
          ((modulePullbackCompIso B S hS f g).hom.app F ⊗ₘ
            (modulePullbackCompIso B S hS f g).hom.app G) := by
  have key := Stacks.SheafOfModules.pullbackModulesCompIso_inv_app_comp_pullbackTensorIso_hom_app
    (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) (pushforwardSetCompNatIso B S hS f g)
    (fSharpSetComp_smallEtaleRingedToposModulesHom B S hS f g) F G
  have hc := modulePullbackCompIso_hom_eq B S hS f g
  have hh := comp_tensor_of_readings (modulePullback B S hS g) (modulePullback B S hS f)
    (modulePullback B S hS (f ≫ g)) (modulePullbackCompIso B S hS f g).hom
    (smallEtalePullbackModulesCompIso B S hS f g).inv hc
    (modulesTensorObjIso B S hS Z.1 Z.2 F G)
    (modulesTensorObjIso B S hS Y.1 Y.2 ((modulePullback B S hS g).obj F)
      ((modulePullback B S hS g).obj G))
    ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).app
      (F, G))
    (modulesTensorObjIso B S hS X.1 X.2
      ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj F))
      ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj G)))
    ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).app
      ((modulePullback B S hS g).obj F, (modulePullback B S hS g).obj G))
    (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS (f ≫ g)).obj F)
      ((modulePullback B S hS (f ≫ g)).obj G))
    ((Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS (f ≫ g))).app (F, G))
    ((modulePullbackCompIso B S hS f g).hom.app F ⊗ₘ
      (modulePullbackCompIso B S hS f g).hom.app G) _
    (congrArg₂ (· ⊗ₘ ·) (NatTrans.congr_app hc F) (NatTrans.congr_app hc G)) _ key
    (modulesTensorObjIso_hom_naturality B S hS _ _)
  exact hh

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullbackUnflatten_pullbackTransport_tensor`, at variables. -/
private theorem unflatten_tensor_of_readings {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    {A₁₂ A' A₁ A₂ B₁₂ B' B₁ B₂ AF₁₂ AF₁ AF₂ BF₁₂ BF₁ BF₂ : 𝒞}
    (cA₁₂ : A₁₂ ⟶ AF₁₂) (cA₁ : A₁ ⟶ AF₁) (cA₂ : A₂ ⟶ AF₂)
    (cB₁₂ : B₁₂ ⟶ BF₁₂) (cB₁ : B₁ ⟶ BF₁) (cB₂ : B₂ ⟶ BF₂)
    (iB₁₂ : BF₁₂ ⟶ B₁₂) (iB₁ : BF₁ ⟶ B₁) (iB₂ : BF₂ ⟶ B₂)
    (hB₁₂ : iB₁₂ ≫ cB₁₂ = 𝟙 _) (hB₁ : cB₁ ≫ iB₁ = 𝟙 _) (hB₂ : cB₂ ≫ iB₂ = 𝟙 _)
    (tr₁₂ : AF₁₂ ⟶ BF₁₂) (tr₁ : AF₁ ⟶ BF₁) (tr₂ : AF₂ ⟶ BF₂)
    (pa : A₁₂ ⟶ A') (qa : A' ⟶ A₁ ⊗ A₂) (pb : B₁₂ ⟶ B') (qb : B' ⟶ B₁ ⊗ B₂)
    (Ta : AF₁₂ ⟶ AF₁ ⊗ AF₂) (Tb : BF₁₂ ⟶ BF₁ ⊗ BF₂)
    (la : cA₁₂ ≫ Ta = pa ≫ qa ≫ (cA₁ ⊗ₘ cA₂))
    (lb : cB₁₂ ≫ Tb = pb ≫ qb ≫ (cB₁ ⊗ₘ cB₂))
    (ht : tr₁₂ ≫ Tb = Ta ≫ (tr₁ ⊗ₘ tr₂)) :
    pa ≫ qa ≫ ((cA₁ ≫ tr₁ ≫ iB₁) ⊗ₘ (cA₂ ≫ tr₂ ≫ iB₂)) =
      (cA₁₂ ≫ tr₁₂ ≫ iB₁₂) ≫ pb ≫ qb := by
  have lb' : iB₁₂ ≫ pb ≫ qb = Tb ≫ (iB₁ ⊗ₘ iB₂) := by
    have e : iB₁₂ ≫ pb ≫ qb ≫ (cB₁ ⊗ₘ cB₂) ≫ (iB₁ ⊗ₘ iB₂) =
        iB₁₂ ≫ cB₁₂ ≫ Tb ≫ (iB₁ ⊗ₘ iB₂) := by
      rw [reassoc_of% lb]
    simpa only [tensorHom_comp_tensorHom, hB₁, hB₂, id_tensorHom_id, Category.comp_id,
      reassoc_of% hB₁₂] using e
  rw [Category.assoc, Category.assoc, lb', reassoc_of% ht, reassoc_of% la]
  simp only [tensorHom_comp_tensorHom]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Transporting a tensor product along an equality of morphisms is the tensor product of the
transports, through Stacks 03EL. -/
theorem pullbackTransport_tensor {T X : AlgebraicSpaces B S hS} {f g : T ⟶ X} (h : f = g)
    (Y₁ Y₂ : Modules.{u, u} B S hS X.1 X.2) :
    pullbackTransport (Y₁ ⊗ Y₂) h ≫ (modulePullbackTensorIso B S hS g Y₁ Y₂).hom =
      (modulePullbackTensorIso B S hS f Y₁ Y₂).hom ≫
        (pullbackTransport Y₁ h ⊗ₘ pullbackTransport Y₂ h) := by
  subst h
  simp [pullbackTransport]

/-- The comparison `f^*g^*M ⟶ (f ≫ g)^*M` of Stacks 03LU at a module, typed with the iterated
inverse image spelled out, so that the statements below never compare the two spellings of
`f^*g^*M`. -/
def modulePullbackCompHom {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) ⟶
      (modulePullback B S hS (f ≫ g)).obj M :=
  (modulePullbackCompIso B S hS f g).hom.app M

/-- The inverse comparison `(f ≫ g)^*M ⟶ f^*g^*M` of Stacks 03LU at a module. -/
def modulePullbackCompInv {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS (f ≫ g)).obj M ⟶
      (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) :=
  (modulePullbackCompIso B S hS f g).inv.app M

/-- The inverse comparison followed by the comparison is the identity. -/
theorem modulePullbackCompInv_comp_compHom {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    modulePullbackCompInv B S hS f g M ≫ modulePullbackCompHom B S hS f g M = 𝟙 _ :=
  (modulePullbackCompIso B S hS f g).inv_hom_id_app M

/-- The comparison followed by the inverse comparison is the identity. -/
theorem modulePullbackCompHom_comp_compInv {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    modulePullbackCompHom B S hS f g M ≫ modulePullbackCompInv B S hS f g M = 𝟙 _ :=
  (modulePullbackCompIso B S hS f g).hom_inv_id_app M

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_tensor` with the comparisons typed
through `AlgebraicGeometry.Space.modulePullbackCompHom`. -/
theorem modulePullbackCompHom_tensor {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F G : Modules.{u, u} B S hS Z.1 Z.2) :
    modulePullbackCompHom B S hS f g (F ⊗ G) ≫ (modulePullbackTensorIso B S hS (f ≫ g) F G).hom =
      (modulePullback B S hS f).map (modulePullbackTensorIso B S hS g F G).hom ≫
        (modulePullbackTensorIso B S hS f _ _).hom ≫
          (modulePullbackCompHom B S hS f g F ⊗ₘ modulePullbackCompHom B S hS f g G) :=
  modulePullbackCompIso_hom_app_tensor B S hS f g F G

/-- Unflattening, through `AlgebraicGeometry.Space.modulePullbackCompHom` and
`AlgebraicGeometry.Space.modulePullbackCompInv`. -/
theorem modulePullbackUnflatten_eq_compHom {V U X : AlgebraicSpaces B S hS} (φ : U ⟶ X)
    {a b : V ⟶ U} {M : Modules.{u, u} B S hS X.1 X.2}
    (α : (modulePullback B S hS (a ≫ φ)).obj M ⟶ (modulePullback B S hS (b ≫ φ)).obj M) :
    modulePullbackUnflatten φ α =
      modulePullbackCompHom B S hS a φ M ≫ α ≫ modulePullbackCompInv B S hS b φ M :=
  rfl

/-- **Unflattening a transport is monoidal.** For `a, b : V ⟶ U` and `φ : U ⟶ X` with
`a ≫ φ = b ≫ φ`, the identification `a^*φ^*Y ⟶ b^*φ^*Y` obtained by unflattening the transport
along `a ≫ φ = b ≫ φ` is compatible with tensor products through Stacks 03EL. -/
theorem modulePullbackUnflatten_pullbackTransport_tensor {V U X : AlgebraicSpaces B S hS}
    (a b : V ⟶ U) (φ : U ⟶ X) (h : a ≫ φ = b ≫ φ) (Y₁ Y₂ : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS a).map (modulePullbackTensorIso B S hS φ Y₁ Y₂).hom ≫
        (modulePullbackTensorIso B S hS a _ _).hom ≫
          (modulePullbackUnflatten φ (pullbackTransport Y₁ h) ⊗ₘ
            modulePullbackUnflatten φ (pullbackTransport Y₂ h)) =
      modulePullbackUnflatten φ (pullbackTransport (Y₁ ⊗ Y₂) h) ≫
        (modulePullback B S hS b).map (modulePullbackTensorIso B S hS φ Y₁ Y₂).hom ≫
          (modulePullbackTensorIso B S hS b _ _).hom := by
  rw [modulePullbackUnflatten_eq_compHom, modulePullbackUnflatten_eq_compHom,
      modulePullbackUnflatten_eq_compHom]
  exact unflatten_tensor_of_readings _ _ _ _ _ _ _ _ _
    (modulePullbackCompInv_comp_compHom B S hS b φ (Y₁ ⊗ Y₂))
    (modulePullbackCompHom_comp_compInv B S hS b φ Y₁)
    (modulePullbackCompHom_comp_compInv B S hS b φ Y₂) _ _ _ _ _ _ _ _ _
    (modulePullbackCompHom_tensor B S hS a φ Y₁ Y₂)
    (modulePullbackCompHom_tensor B S hS b φ Y₁ Y₂)
    (pullbackTransport_tensor B S hS h Y₁ Y₂)

/-- **The canonical transition morphism of an inverse image to a groupoid is compatible with
tensor products.**  For a groupoid `(U, R, s, t, c)` in algebraic spaces, `φ : U ⟶ X` with
`t ≫ φ = s ≫ φ` and `𝒪_X`-modules `Y₁`, `Y₂`, the canonical transition morphism
`AlgebraicGeometry.Space.spaceBaseDescent` of `φ^*(Y₁ ⊗ Y₂)` is carried, through the comparisons
of Stacks 03EL along `φ`, `t` and `s`, to the tensor product of those of `φ^*Y₁` and `φ^*Y₂`. -/
theorem spaceBaseDescent_tensor {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (Y₁ Y₂ : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS G.target).map (modulePullbackTensorIso B S hS φ Y₁ Y₂).hom ≫
        (modulePullbackTensorIso B S hS G.target _ _).hom ≫
          (spaceBaseDescent B S hS G φ hφ Y₁ ⊗ₘ spaceBaseDescent B S hS G φ hφ Y₂) =
      spaceBaseDescent B S hS G φ hφ (Y₁ ⊗ Y₂) ≫
        (modulePullback B S hS G.source).map (modulePullbackTensorIso B S hS φ Y₁ Y₂).hom ≫
          (modulePullbackTensorIso B S hS G.source _ _).hom :=
  modulePullbackUnflatten_pullbackTransport_tensor B S hS G.target G.source φ hφ Y₁ Y₂

end AlgebraicGeometry.Space

end
