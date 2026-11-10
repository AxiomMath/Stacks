module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSquare
public import
  StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3TensorCompatAssembly
public import
    StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedC3UnitCompatAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SpaceBaseDescentTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackMulComparison

/-!
# The identification of the source of `ψ` on the atlas is monoidal

In Situation 0849 let `π : P ⟶ X` be the relative Proj, `X = U/R` a presentation of the base and
`c : P_U ⟶ P` the atlas of the induced presentation of `P`.  The source `π^*𝒜` of the
homomorphism `ψ` of Stacks 084D is a sheaf of graded algebras with multiplication
`π^*𝒜_i ⊗ π^*𝒜_j ≅ π^*(𝒜_i ⊗ 𝒜_j) ⟶ π^*𝒜_{i+j}` (Stacks 03EL followed by the inverse image of the
multiplication of `𝒜`), and its inverse image along `c` is identified degreewise with the module
attached to `π_U^*(u^*𝒜)_n` (`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso`).
This file proves that this identification carries the multiplication of `c^*π^*𝒜` to the
multiplication `π_U^*Z_i ⊗ π_U^*Z_j ≅ π_U^*(Z_i ⊗ Z_j) ⟶ π_U^*Z_{i+j}` on the chart side, for
any multiplication of the Zariski readings `Z_n` of `u^*𝒜_n` that the identification
`u^*𝒜_n ≅ (Z_n)^a` (`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`) carries the
multiplication of `u^*𝒜` to; likewise for the units.

## Main results

* `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app`
  says that the comparison `f^*g^* ≅ (f ≫ g)^*` of Stacks 03LU carries the iterated pulled-back
  multiplication to the pulled-back multiplication.
* `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_comp_eqToIso`: the same for the
  transport along an equality of morphisms.
* `AlgebraicGeometry.Space.modulePullbackTensorIso_inv_comp_map_mulSheaf`: the multiplication of
  the pullback of a sheaf of graded algebras is the pulled-back multiplication, read through
  Stacks 03EL for a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_mul`: the
  identification `g^*(M^a) ≅ (g^*M)^a` carries the pulled-back multiplication to the
  multiplication `g^*M ⊗ g^*N ≅ g^*(M ⊗ N) ⟶ g^*K`.
* `AlgebraicGeometry.Space.ZariskiReadingIsoMulCompat`: the identification `N ≅ (N_Zar)^a` of a
  sheaf of graded algebras carries its multiplication to a given multiplication of the readings.
* `AlgebraicGeometry.Space.modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_mul`:
  then `g^*f^*𝒜_n ≅ g^*(Z_n^a) ≅ (g^*Z_n)^a` is multiplicative.
* `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_mul`: **the
  identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas
  (`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso`, written as the composite of its
  factors by `…chartPullbackIso_eq_trans_yonedaSpace`) is multiplicative.**
* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app`,
  `…modulePullbackUnitIso_inv_comp_map_comp_eqToIso`,
  `…modulePullbackRepresentedQuasicoherentIso_hom_one`: the unit companions of the first, second
  and fourth results, with the pulled-back unit `𝒪 ≅ f^*𝒪 ⟶ f^*K` (Stacks 03LU) in place of the
  pulled-back multiplication.
* `AlgebraicGeometry.Space.ZariskiReadingIsoOneCompat`: the identification `N ≅ (N_Zar)^a` carries
  a given morphism out of the structure sheaf to a given morphism of the readings.
* `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_one`: **the composite of
  the factors of the identification `c^*π^*𝒜_0 ≅ (π_U^*Z_0)^a` is unital.**

## Implementation notes

Every step is proved at free variables and instantiated once.  The spellings of the inverse images
and of the represented algebraic space of `U` are chosen so that the instances match
syntactically: the space of `U` is `AlgebraicGeometry.Space.yonedaSpace` (the spelling of
`AlgebraicGeometry.Space.etalePointAlgebra`), the comparisons of Stacks 03LU are read with the
iterated inverse image as source, and the sheafification instances of the small étale site are
those at the universe of the modules.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

section Abstract

variable {D : Type*} [cD : Category D] [mD : MonoidalCategory D]

/-- Two multiplicative families compose to a multiplicative family. -/
theorem mulSquare_comp {Xi Xj Xk Yi Yj Yk Zi Zj Zk : D}
    (μX : Xi ⊗ Xj ⟶ Xk) (μY : Yi ⊗ Yj ⟶ Yk) (μZ : Zi ⊗ Zj ⟶ Zk)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (fk : Xk ⟶ Yk) (gi : Yi ⟶ Zi) (gj : Yj ⟶ Zj) (gk : Yk ⟶ Zk)
    (hf : μX ≫ fk = (fi ⊗ₘ fj) ≫ μY) (hg : μY ≫ gk = (gi ⊗ₘ gj) ≫ μZ) :
    μX ≫ fk ≫ gk = ((fi ≫ gi) ⊗ₘ (fj ≫ gj)) ≫ μZ := by
  rw [reassoc_of% hf, hg, tensorHom_comp_tensorHom_assoc]

/-- The inverse of a multiplicative family of isomorphisms is multiplicative. -/
theorem mulSquare_inv {Xi Xj Xk Yi Yj Yk : D}
    (μX : Xi ⊗ Xj ⟶ Xk) (μY : Yi ⊗ Yj ⟶ Yk) (ei : Xi ≅ Yi) (ej : Xj ≅ Yj) (ek : Xk ≅ Yk)
    (h : μX ≫ ek.hom = (ei.hom ⊗ₘ ej.hom) ≫ μY) :
    μY ≫ ek.inv = (ei.inv ⊗ₘ ej.inv) ≫ μX := by
  rw [Iso.comp_inv_eq, Category.assoc, h, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    Iso.inv_hom_id, id_tensorHom_id, Category.id_comp]

/-- **A composite of four multiplicative families is multiplicative**: if
`σ_n = a_n ≪≫ b_n ≪≫ c_n⁻¹ ≪≫ e_n` and the composite of the four factors carries `T⁻¹ ≫ x` to `μ`,
then `x ≫ σ_{i+j} = T ≫ (σ_i ⊗ σ_j) ≫ μ`. -/
theorem mul_of_trans_four_of_comp
    {Y X0i X0j X0k X1i X1j X1k X2i X2j X2k X3i X3j X3k X4i X4j X4k : D}
    {σi : X0i ≅ X4i} {σj : X0j ≅ X4j} {σk : X0k ≅ X4k}
    {ai : X0i ≅ X1i} {aj : X0j ≅ X1j} {ak : X0k ≅ X1k}
    {bi : X1i ≅ X2i} {bj : X1j ≅ X2j} {bk : X1k ≅ X2k}
    {ci : X3i ≅ X2i} {cj : X3j ≅ X2j} {ck : X3k ≅ X2k}
    {ei : X3i ≅ X4i} {ej : X3j ≅ X4j} {ek : X3k ≅ X4k}
    (hσi : σi = ai ≪≫ bi ≪≫ ci.symm ≪≫ ei)
    (hσj : σj = aj ≪≫ bj ≪≫ cj.symm ≪≫ ej)
    (hσk : σk = ak ≪≫ bk ≪≫ ck.symm ≪≫ ek)
    {T : Y ≅ X0i ⊗ X0j} {x : Y ⟶ X0k} {μ4 : X4i ⊗ X4j ⟶ X4k}
    (h : (T.inv ≫ x) ≫ ak.hom ≫ bk.hom ≫ ck.inv ≫ ek.hom =
      ((ai.hom ≫ bi.hom ≫ ci.inv ≫ ei.hom) ⊗ₘ (aj.hom ≫ bj.hom ≫ cj.inv ≫ ej.hom)) ≫ μ4) :
    x ≫ σk.hom = T.hom ≫ (σi.hom ⊗ₘ σj.hom) ≫ μ4 := by
  subst hσi hσj hσk
  rw [← Iso.inv_comp_eq]
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using h

end Abstract

section Square

/-- The image under a functor of a pulled-back multiplication through an isomorphism; at
variables. -/
private theorem inv_comp_map_comp_of_hom_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b k : C} {x y : D} (e : a ≅ b) (μ : b ⟶ k) (P : F.obj b ≅ x) (e' : y ≅ x)
    (μ' : x ⟶ F.obj k) (h : P.hom ≫ μ' = F.map μ) :
    (F.mapIso e ≪≫ P ≪≫ e'.symm).inv ≫ F.map (e.hom ≫ μ) = e'.hom ≫ μ' := by
  rw [F.map_comp, ← h]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id, F.map_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- The square of `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_mul`, at
variables. -/
private theorem inv_comp_map_comp_of_compat {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {a b k : C} {x y z w r : D} (TE : a ≅ b) (em : a ⟶ k) (Tp : P.obj b ≅ x) (cc : x ⟶ r)
    (cMN : P.obj a ⟶ y) (cK : P.obj k ⟶ z) (φ : y ⟶ w) (ψ : w ⟶ y) (hφψ : φ ≫ ψ = 𝟙 y)
    (TE' : w ≅ r) (em' : y ⟶ z) (emc : w ⟶ z) (hemc : emc = ψ ≫ em')
    (hcompat : P.map TE.hom ≫ Tp.hom ≫ cc = cMN ≫ φ ≫ TE'.hom)
    (hnat : P.map em ≫ cK = cMN ≫ em') :
    (Tp.inv ≫ P.map (TE.inv ≫ em)) ≫ cK = cc ≫ TE'.inv ≫ emc := by
  have hc : cMN = P.map TE.hom ≫ Tp.hom ≫ cc ≫ TE'.inv ≫ ψ := by
    rw [reassoc_of% hcompat, Iso.hom_inv_id_assoc, hφψ, Category.comp_id]
  rw [Category.assoc, P.map_comp, Category.assoc, hnat, hc, hemc]
  simp only [Category.assoc, ← P.map_comp_assoc, Iso.inv_hom_id, P.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc]

/-- A comparison `F ∘ G ≅ H` of functors carries `F(T⁻¹ ≫ m)` to `T'⁻¹ ≫ m'`, given the
compatibility of the comparison with `T`, `T'` and its naturality; at variables. -/
private theorem inv_comp_map_comp_of_tensor {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b k : C} {q2 r1 r2 rk : D} (Tg : a ≅ b) (gm : a ⟶ k) (Tf : F.obj b ≅ q2)
    (cA : F.obj a ⟶ r1) (cK : F.obj k ⟶ rk) (cc : q2 ⟶ r2) (Tfg : r1 ≅ r2) (fgm : r1 ⟶ rk)
    (key : cA ≫ Tfg.hom = F.map Tg.hom ≫ Tf.hom ≫ cc) (nat : F.map gm ≫ cK = cA ≫ fgm) :
    (Tf.inv ≫ F.map (Tg.inv ≫ gm)) ≫ cK = cc ≫ Tfg.inv ≫ fgm := by
  simpa only [Category.id_comp] using inv_comp_map_comp_of_compat F Tg gm Tf cc cA cK (𝟙 r1)
    (𝟙 r1) (Category.id_comp _) Tfg fgm fgm (Category.id_comp _).symm
    (by simpa only [Category.id_comp] using key.symm) nat

/-- The underlying morphism of the image of a composite under a functor into a full
subcategory. -/
private theorem map_comp_hom {C D : Type*} [Category C] [Category D] {P : ObjectProperty D}
    (F : C ⥤ P.FullSubcategory) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    (F.map (f ≫ g)).hom = (F.map f).hom ≫ (F.map g).hom := by
  rw [F.map_comp]
  rfl

/-- The underlying morphisms of the images of an isomorphism and its inverse under a functor into
a full subcategory compose to the identity. -/
private theorem map_hom_comp_map_inv_hom {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {a b : C} (e : a ≅ b) :
    (F.map e.hom).hom ≫ (F.map e.inv).hom = 𝟙 (F.obj a).obj := by
  rw [← map_comp_hom, e.hom_inv_id, F.map_id]
  rfl

end Square

section UnitSquares

/-- Two unit squares compose. -/
theorem unitSquare_comp {C : Type*} [Category C] {O X Y Z : C} (u : O ⟶ X) (v : O ⟶ Y)
    (w : O ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : u ≫ f = v) (hg : v ≫ g = w) :
    u ≫ f ≫ g = w := by
  rw [reassoc_of% hf, hg]

/-- The inverse of an isomorphism carrying `u` to `v` carries `v` to `u`. -/
theorem unitSquare_inv {C : Type*} [Category C] {O X Y : C} (u : O ⟶ X) (v : O ⟶ Y)
    (e : X ≅ Y) (h : u ≫ e.hom = v) : v ≫ e.inv = u := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A family of isomorphisms equal to a composite of four factors carries `x` to `μ` when the
composite does.** -/
theorem comp_hom_eq_of_trans {C : Type*} [Category C] {Y X0 X1 X2 X3 X4 : C}
    {a : X0 ≅ X1} {b : X1 ≅ X2} {c : X3 ≅ X2} {e : X3 ≅ X4} {x : Y ⟶ X0} {μ : Y ⟶ X4}
    (h : x ≫ a.hom ≫ b.hom ≫ c.inv ≫ e.hom = μ) (σ : X0 ≅ X4)
    (hσ : σ = a ≪≫ b ≪≫ c.symm ≪≫ e) : x ≫ σ.hom = μ := by
  subst hσ
  exact h

/-- The square of `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_one`, at
variables. -/
private theorem unit_inv_comp_map_comp_of_compat {C D : Type*} [Category C] [Category D]
    (P : C ⥤ D) {a b k : C} {o y w z : D} (rU : a ≅ b) (eu : a ⟶ k) (mU : P.obj b ≅ o)
    (m1 : P.obj a ⟶ y) (mK : P.obj k ⟶ z) (φ : y ⟶ w) (ψ : w ⟶ y) (hφψ : φ ≫ ψ = 𝟙 y)
    (rV : w ≅ o) (eu' : y ⟶ z) (emc : w ⟶ z) (hemc : emc = ψ ≫ eu')
    (hC3 : P.map rU.hom ≫ mU.hom = m1 ≫ φ ≫ rV.hom) (hnat : P.map eu ≫ mK = m1 ≫ eu') :
    (mU.inv ≫ P.map (rU.inv ≫ eu)) ≫ mK = rV.inv ≫ emc := by
  simpa only [Category.comp_id, Category.id_comp] using inv_comp_map_comp_of_compat P rU eu mU
    (𝟙 o) m1 mK φ ψ hφψ rV eu' emc hemc (by simpa only [Category.comp_id] using hC3) hnat

/-- **A comparison `G ⋙ F ≅ H` compatible with identifications of units carries the iterated
image of a morphism out of the unit to its image**: if `cI⁻¹ ≫ F(mG) ≫ mF = mH` at the unit `o`,
then `(mF⁻¹ ≫ F(mG⁻¹ ≫ G(u))) ≫ cI_K = mH⁻¹ ≫ H(u)` for every `u : o ⟶ K`. -/
theorem unitSquare_of_compIso {C D E : Type*} [Category C] [Category D]
    [Category E] {G : C ⥤ D} {F : D ⥤ E} {H : C ⥤ E} {cI : G ⋙ F ≅ H} {oC : C} {oD : D}
    {oE : E} {mG : G.obj oC ≅ oD} {mF : F.obj oD ≅ oE} {mH : H.obj oC ≅ oE}
    (h1 : cI.inv.app oC ≫ F.map mG.hom ≫ mF.hom = mH.hom) {K : C} (u : oC ⟶ K) :
    (mF.inv ≫ F.map (mG.inv ≫ G.map u)) ≫ Iso.hom (X := F.obj (G.obj K)) (cI.app K) =
      mH.inv ≫ H.map u := by
  obtain rfl : mH = (cI.app oC).symm ≪≫ F.mapIso mG ≪≫ mF := Iso.ext h1.symm
  have nat : F.map (G.map u) ≫ cI.hom.app K = cI.hom.app oC ≫ H.map u := cI.hom.naturality u
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
    Functor.map_comp]
  rw [nat]

/-- A functor carries a commutative triangle under a fixed morphism to a commutative triangle. -/
private theorem comp_map_comp_map_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {o : D} {a b c : C} (e : o ⟶ F.obj a) {u : a ⟶ b} {v : a ⟶ c} {z : b ⟶ c} (h : u ≫ z = v) :
    (e ≫ F.map u) ≫ F.map z = e ≫ F.map v := by
  rw [Category.assoc, ← F.map_comp, h]

end UnitSquares

attribute [local instance] modulesMonoidalCategory

/- The sheafification instances of the small étale site at the universe of the modules; the
general instances at the coefficient universe `max (u + 1) z` leave instance search with an
unsolvable universe constraint. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Spaces

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison `f^*g^* ≅ (f ≫ g)^*` of Stacks 03LU carries the iterated pulled-back
multiplication to the pulled-back multiplication**: for `m : F ⊗ G ⟶ K` of `𝒪_Z`-modules, the
morphism `f^*g^*F ⊗ f^*g^*G ≅ f^*(g^*F ⊗ g^*G) ≅ f^*g^*(F ⊗ G) ⟶ f^*g^*K` followed by the
comparison at `K` is the tensor product of the comparisons at `F` and `G` followed by
`(f ≫ g)^*F ⊗ (f ≫ g)^*G ≅ (f ≫ g)^*(F ⊗ G) ⟶ (f ≫ g)^*K`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app
    (f : X ⟶ Y) (g : Y ⟶ Z) (F G K : Modules.{u, u} B S hS Z.1 Z.2) (m : F ⊗ G ⟶ K) :
    ((modulePullbackTensorIso B S hS f ((modulePullback B S hS g).obj F)
        ((modulePullback B S hS g).obj G)).inv ≫
      (modulePullback B S hS f).map ((modulePullbackTensorIso B S hS g F G).inv ≫
        (modulePullback B S hS g).map m)) ≫
      Iso.hom (X := (modulePullback B S hS f).obj ((modulePullback B S hS g).obj K))
        ((modulePullbackCompIso B S hS f g).app K) =
    (Iso.hom (X := (modulePullback B S hS f).obj ((modulePullback B S hS g).obj F))
        ((modulePullbackCompIso B S hS f g).app F) ⊗ₘ
        Iso.hom (X := (modulePullback B S hS f).obj ((modulePullback B S hS g).obj G))
        ((modulePullbackCompIso B S hS f g).app G)) ≫
      (modulePullbackTensorIso B S hS (f ≫ g) F G).inv ≫ (modulePullback B S hS (f ≫ g)).map m :=
  inv_comp_map_comp_of_tensor (modulePullback B S hS f) (modulePullbackTensorIso B S hS g F G)
    ((modulePullback B S hS g).map m) _ ((modulePullbackCompIso B S hS f g).hom.app (F ⊗ G))
    ((modulePullbackCompIso B S hS f g).hom.app K) _ (modulePullbackTensorIso B S hS (f ≫ g) F G)
    ((modulePullback B S hS (f ≫ g)).map m)
    (modulePullbackCompIso_hom_app_tensor B S hS f g F G)
    ((modulePullbackCompIso B S hS f g).hom.naturality m)

/-- **Equal morphisms have the same pulled-back multiplication**: for `h : f = f'`, the
transports `f^*F ≅ f'^*F` carry `f^*F ⊗ f^*G ≅ f^*(F ⊗ G) ⟶ f^*K` to the same morphism for `f'`. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_eqToIso {f f' : X ⟶ Y} (h : f = f')
    (F G K : Modules.{u, u} B S hS Y.1 Y.2) (m : F ⊗ G ⟶ K) :
    ((modulePullbackTensorIso B S hS f F G).inv ≫ (modulePullback B S hS f).map m) ≫
      (eqToIso (congrArg (fun f => (modulePullback B S hS f).obj K) h)).hom =
    ((eqToIso (congrArg (fun f => (modulePullback B S hS f).obj F) h)).hom ⊗ₘ
        (eqToIso (congrArg (fun f => (modulePullback B S hS f).obj G) h)).hom) ≫
      (modulePullbackTensorIso B S hS f' F G).inv ≫ (modulePullback B S hS f').map m := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, id_tensorHom_id, Category.id_comp]

/-- **The inverse image of a multiplicative square is multiplicative**: if `m ≫ ζ_k = (ζ_i ⊗ ζ_j) ≫
m'` for `𝒪_Y`-modules, then the same holds for the inverse images along `f`, the multiplications
read through Stacks 03EL. -/
theorem modulePullbackTensorIso_inv_comp_map_comp_map_of_comp_eq (f : X ⟶ Y)
    {Mi Mj Mk Ni Nj Nk : Modules.{u, u} B S hS Y.1 Y.2} (m : Mi ⊗ Mj ⟶ Mk) (m' : Ni ⊗ Nj ⟶ Nk)
    (zi : Mi ⟶ Ni) (zj : Mj ⟶ Nj) (zk : Mk ⟶ Nk) (h : m ≫ zk = (zi ⊗ₘ zj) ≫ m') :
    ((modulePullbackTensorIso B S hS f Mi Mj).inv ≫ (modulePullback B S hS f).map m) ≫
        (modulePullback B S hS f).map zk =
      ((modulePullback B S hS f).map zi ⊗ₘ (modulePullback B S hS f).map zj) ≫
        (modulePullbackTensorIso B S hS f Ni Nj).inv ≫ (modulePullback B S hS f).map m' := by
  have nat := modulePullbackTensorIso_hom_naturality B S hS f zi zj
  have nat' : (modulePullbackTensorIso B S hS f Mi Mj).inv ≫
      (modulePullback B S hS f).map (zi ⊗ₘ zj) =
      ((modulePullback B S hS f).map zi ⊗ₘ (modulePullback B S hS f).map zj) ≫
        (modulePullbackTensorIso B S hS f Ni Nj).inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% nat, Iso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, ← (modulePullback B S hS f).map_comp, h,
    (modulePullback B S hS f).map_comp, reassoc_of% nat']

/-- **The multiplication of the pullback of a sheaf of graded algebras is the pulled-back
multiplication** (Stacks 03EL for a morphism of algebraic spaces): for `f : X ⟶ Y` and a sheaf
of graded algebras `𝒜` on `Y`, `f^*𝒜_i ⊗ f^*𝒜_j ≅ f^*(𝒜_i ⊗ 𝒜_j) ⟶ f^*𝒜_{i+j}` is the
multiplication of `f^*𝒜`. -/
theorem modulePullbackTensorIso_inv_comp_map_mulSheaf
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Y)) (f : X ⟶ Y)
    (i j : ℤ) :
    (modulePullbackTensorIso B S hS f (A.piece i) (A.piece j)).inv ≫
      (modulePullback B S hS f).map
        ((modulesTensorObjIso B S hS Y.1 Y.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j) =
    (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj (A.piece i))
        ((modulePullback B S hS f).obj (A.piece j))).hom ≫
      SheafOfModules.GradedAlgebra.mulSheaf
        ((Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull
          (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
          (smallEtaleRingedToposHom B S hS f)).obj A) i j :=
  inv_comp_map_comp_of_hom_comp (modulePullback B S hS f)
    (modulesTensorObjIso B S hS Y.1 Y.2 (A.piece i) (A.piece j))
    (SheafOfModules.GradedAlgebra.mulSheaf A i j)
    ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS f)).app
      (A.piece i, A.piece j))
    (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj (A.piece i))
        ((modulePullback B S hS f).obj (A.piece j)))
    _ (Stacks.Sheaves.GradedAlgebraPullback.pullbackTensorIso_hom_app_comp_mulSheaf
      (smallEtaleRingedToposModulesHom B S hS f) A i j)

end Spaces

section SpacesUnit

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison `f^*g^* ≅ (f ≫ g)^*` of Stacks 03LU carries the iterated pulled-back unit to
the pulled-back unit**: for `u : 𝒪_Z ⟶ K`, the morphism `𝒪_X ≅ f^*𝒪_Y ≅ f^*g^*𝒪_Z ⟶ f^*g^*K`
followed by the comparison at `K` is `𝒪_X ≅ (f ≫ g)^*𝒪_Z ⟶ (f ≫ g)^*K`.  The statement is the
type of its proof. -/
theorem modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : Modules.{u, u} B S hS Z.1 Z.2)
    (u : SheafOfModules.unit (structureRingSheaf B S hS Z) ⟶ K) :
    type_of% (unitSquare_of_compIso
      (modulePullbackCompIso_inv_app_unit_comp f g) (K := K) u) :=
  unitSquare_of_compIso (modulePullbackCompIso_inv_app_unit_comp f g) (K := K) u

/-- **Equal morphisms have the same pulled-back unit**: for `h : f = f'`, the transport
`f^*K ≅ f'^*K` carries `𝒪_X ≅ f^*𝒪_Y ⟶ f^*K` to the same morphism for `f'`. -/
theorem modulePullbackUnitIso_inv_comp_map_comp_eqToIso {f f' : X ⟶ Y} (h : f = f')
    (K : Modules.{u, u} B S hS Y.1 Y.2)
    (u : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ K) :
    ((modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map u) ≫
      (eqToIso (congrArg (fun f => (modulePullback B S hS f).obj K) h)).hom =
    (modulePullbackUnitIso B S hS f').inv ≫ (modulePullback B S hS f').map u := by
  subst h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

/-- **The inverse image of a unit square is a unit square**: if `u ≫ z = v` for `𝒪_Y`-modules,
then the same holds for the pulled-back units along `f`. -/
theorem modulePullbackUnitIso_inv_comp_map_comp_map_of_comp_eq (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (u : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M)
    (v : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N) (z : M ⟶ N)
    (h : u ≫ z = v) :
    ((modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map u) ≫
        (modulePullback B S hS f).map z =
      (modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map v :=
  comp_map_comp_map_of_comp_eq (modulePullback B S hS f) _ h

end SpacesUnit


section Represented

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) carries the pulled-back
multiplication to the pulled-back multiplication**: for a morphism `g : V ⟶ U` of the site and
a morphism `m : M ⊗ N ⟶ K` of quasi-coherent modules on the scheme of `U`, the morphism
`g^*(M^a) ⊗ g^*(N^a) ≅ g^*(M^a ⊗ N^a) ⟶ g^*(K^a)` attached to `m` followed by the identification
at `K` is the tensor product of the identifications at `M` and `N` followed by the morphism
attached to `g^*M ⊗ g^*N ≅ g^*(M ⊗ N) ⟶ g^*K`. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_mul {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    ((modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).inv ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedTensorChartMul B S hS m)) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ⊗ₘ
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom) ≫
      representedTensorChartMul B S hS
        ((quasicoherentPullbackTensorIso B S hS g M N).inv ≫ quasicoherentPullbackMap B S hS g m) :=
  inv_comp_map_comp_of_compat (modulePullback B S hS (representedSpaceMap B S hS g))
    (representedQuasicoherentSchemeTensorIso B S hS U M N)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom _ _
    (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentTensorObj B S hS U M N)).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackTensorIso B S hS g M N).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackTensorIso B S hS g M N).inv).hom
    (map_hom_comp_map_inv_hom _ _)
    (representedQuasicoherentSchemeTensorIso B S hS V (quasicoherentPullbackObj B S hS g M)
      (quasicoherentPullbackObj B S hS g N))
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackMap B S hS g m)).hom _
    (map_comp_hom _ _ _)
    (representedC3TensorCompat B S hS g M N)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS g m)

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_mul` with the
represented algebraic space of `U` spelled `AlgebraicGeometry.Space.yonedaSpace`. -/
private theorem modulePullbackRepresentedQuasicoherentIso_hom_mul_yonedaSpace
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    ((modulePullbackTensorIso B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).inv ≫
      (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)).map
        (representedTensorChartMul B S hS m)) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ⊗ₘ
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom) ≫
      representedTensorChartMul B S hS
        ((quasicoherentPullbackTensorIso B S hS g M N).inv ≫ quasicoherentPullbackMap B S hS g m) :=
  modulePullbackRepresentedQuasicoherentIso_hom_mul B S hS g m

end Represented

section RepresentedUnit

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) carries the pulled-back unit to
the pulled-back unit**: for a morphism `g : V ⟶ U` of the site and `u : 𝒪_U ⟶ K` of
quasi-coherent modules on the scheme of `U`, the morphism `𝒪 ≅ g^*𝒪 ≅ g^*((𝒪_U)^a) ⟶ g^*(K^a)`
attached to `u` (`AlgebraicGeometry.Space.representedUnitChartHom`), followed by the
identification at `K`, is the morphism attached to `𝒪_V ≅ g^*𝒪_U ⟶ g^*K`. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_one {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (u : quasicoherentUnitObj B S hS U ⟶ K) :
    ((modulePullbackUnitIso B S hS (representedSpaceMap B S hS g)).inv ≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).map
        (representedUnitChartHom B S hS u)) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    representedUnitChartHom B S hS
      ((quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g u) :=
  unit_inv_comp_map_comp_of_compat (modulePullback B S hS (representedSpaceMap B S hS g))
    (representedQuasicoherentSchemeUnitIso B S hS U)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map u).hom _
    (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentUnitObj B S hS U)).hom
    (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).hom).hom
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackUnitIso B S hS g).inv).hom
    (map_hom_comp_map_inv_hom _ _)
    (representedQuasicoherentSchemeUnitIso B S hS V)
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackMap B S hS g u)).hom _
    (map_comp_hom _ _ _)
    (representedC3UnitCompat B S hS g)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS g u)

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_one` with the
represented algebraic space of `U` spelled `AlgebraicGeometry.Space.yonedaSpace`. -/
private theorem modulePullbackRepresentedQuasicoherentIso_hom_one_yonedaSpace
    {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (u : quasicoherentUnitObj B S hS U ⟶ K) :
    ((modulePullbackUnitIso B S hS (X := yonedaSpace B S hS U)
        (representedSpaceMap B S hS g)).inv ≫
      (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)).map
        (representedUnitChartHom B S hS u)) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS g K).hom =
    representedUnitChartHom B S hS
      ((quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g u) :=
  modulePullbackRepresentedQuasicoherentIso_hom_one B S hS g u

end RepresentedUnit

/-- Rewriting the first factor of a composite by an equation with a two-step composite. -/
private theorem comp_eq_of_eq_comp {C : Type*} [Category C] {a b c d : C} {x : a ⟶ c}
    {y₁ : a ⟶ b} {y₂ : b ⟶ c} {z : c ⟶ d} {w : a ⟶ d} (e : x = y₁ ≫ y₂)
    (h : y₁ ≫ y₂ ≫ z = w) : x ≫ z = w := by
  rw [e, Category.assoc, h]

section Zariski

/-- **The identification `N ≅ (N_Zar)^a` of a sheaf of graded algebras with the modules attached
to its Zariski readings carries its multiplication to `m`**: for a sheaf of graded algebras `G` on
the represented algebraic space of `T` whose pieces in degrees `i`, `j`, `i + j` are
quasi-coherent, and a morphism `m : Z_i ⊗ Z_j ⟶ Z_{i+j}` of the Zariski readings
(`AlgebraicGeometry.Space.zariskiReadingQcoh`), the multiplication `G_i ⊗ G_j ⟶ G_{i+j}` followed
by `AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` in degree `i + j` is the tensor product
of the identifications in degrees `i` and `j` followed by the morphism `Z_i^a ⊗ Z_j^a ⟶ Z_{i+j}^a`
attached to `m` (`AlgebraicGeometry.Space.representedTensorChartMul`). -/
def ZariskiReadingIsoMulCompat (T : BigFppfOver B S hS)
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))
    (i j : ℤ) (hi : (G.piece i).IsQuasicoherentOnSite) (hj : (G.piece j).IsQuasicoherentOnSite)
    (hk : (G.piece (i + j)).IsQuasicoherentOnSite)
    (m : quasicoherentTensorObj B S hS T (zariskiReadingQcoh T (G.piece i) hi)
        (zariskiReadingQcoh T (G.piece j) hj) ⟶ zariskiReadingQcoh T (G.piece (i + j)) hk) :
    Prop :=
  (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) (G.piece i)
      (G.piece j)).hom ≫ SheafOfModules.GradedAlgebra.mulSheaf G i j ≫
      (zariskiReadingQuasicoherentIso T (G.piece (i + j)) hk).hom =
    ((zariskiReadingQuasicoherentIso T (G.piece i) hi).hom ⊗ₘ
        (zariskiReadingQuasicoherentIso T (G.piece j) hj).hom) ≫
      representedTensorChartMul B S hS m

/-- **The restriction to a scheme point carries the multiplication of `𝒜` to `m`**: if the
identification of `u^*𝒜` with the modules attached to its Zariski readings carries the
multiplication of `u^*𝒜` to `m` (`AlgebraicGeometry.Space.ZariskiReadingIsoMulCompat`), then it
carries the pulled-back multiplication `u^*𝒜_i ⊗ u^*𝒜_j ≅ u^*(𝒜_i ⊗ 𝒜_j) ⟶ u^*𝒜_{i+j}` to the
morphism attached to `m`. -/
theorem modulePullbackTensorIso_inv_comp_map_mulSheaf_comp_zariskiReadingQuasicoherentIso
    {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (i j : ℤ)
    (hi : ((etalePointAlgebra A T f).piece i).IsQuasicoherentOnSite)
    (hj : ((etalePointAlgebra A T f).piece j).IsQuasicoherentOnSite)
    (hk : ((etalePointAlgebra A T f).piece (i + j)).IsQuasicoherentOnSite)
    (m : quasicoherentTensorObj B S hS T
        (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece i) hi)
        (zariskiReadingQcoh T ((etalePointAlgebra A T f).piece j) hj) ⟶
      zariskiReadingQcoh T ((etalePointAlgebra A T f).piece (i + j)) hk)
    (h : ZariskiReadingIsoMulCompat B S hS T (etalePointAlgebra A T f) i j hi hj hk m) :
    ((modulePullbackTensorIso B S hS (pointHom f) (A.piece i) (A.piece j)).inv ≫
      (modulePullback B S hS (pointHom f)).map
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j)) ≫
      (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece (i + j)) hk).hom =
    MonoidalCategoryStruct.tensorHom
        (C := Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece i) hi).hom
        (zariskiReadingQuasicoherentIso T ((etalePointAlgebra A T f).piece j) hj).hom ≫
      representedTensorChartMul B S hS m :=
  comp_eq_of_eq_comp (modulePullbackTensorIso_inv_comp_map_mulSheaf B S hS A (pointHom f) i j) h

end Zariski

section PointChart

/-- **The inverse image along `π_U` of the identification `u^*𝒜_n ≅ (Z_n)^a`, followed by
`π_U^*(Z_n^a) ≅ (π_U^*Z_n)^a`, is multiplicative**: for a morphism `g : V ⟶ U` of the site, a
scheme point `f : U ⟶ X` and a multiplication `m` of the Zariski readings `Z_n` of `f^*𝒜_n` that
the identification `f^*𝒜_n ≅ (Z_n)^a` carries the multiplication of `f^*𝒜` to, the composite
`g^*f^*𝒜_n ≅ g^*(Z_n^a) ≅ (g^*Z_n)^a` carries the twice pulled-back multiplication of `𝒜` to
`g^*Z_i ⊗ g^*Z_j ≅ g^*(Z_i ⊗ Z_j) ⟶ g^*Z_{i+j}`. -/
theorem modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_mul
    {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {V U : BigFppfOver B S hS} (g : V ⟶ U) (f : yoneda.obj U ⟶ X.1) (i j : ℤ)
    (hi : ((etalePointAlgebra A U f).piece i).IsQuasicoherentOnSite)
    (hj : ((etalePointAlgebra A U f).piece j).IsQuasicoherentOnSite)
    (hk : ((etalePointAlgebra A U f).piece (i + j)).IsQuasicoherentOnSite)
    (m : quasicoherentTensorObj B S hS U
        (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece i) hi)
        (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece j) hj) ⟶
      zariskiReadingQcoh U ((etalePointAlgebra A U f).piece (i + j)) hk)
    (h : ZariskiReadingIsoMulCompat B S hS U (etalePointAlgebra A U f) i j hi hj hk m) :
    ((modulePullbackTensorIso B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)
        ((modulePullback B S hS (pointHom f)).obj (A.piece i))
        ((modulePullback B S hS (pointHom f)).obj (A.piece j))).inv ≫
      (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)).map
        ((modulePullbackTensorIso B S hS (pointHom f) (A.piece i) (A.piece j)).inv ≫
          (modulePullback B S hS (pointHom f)).map
            ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
              SheafOfModules.GradedAlgebra.mulSheaf A i j))) ≫
      (Functor.mapIso (X := (modulePullback B S hS (pointHom f)).obj (A.piece (i + j)))
          (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g))
          (zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U f).piece (i + j)) hk) ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS g
          (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece (i + j)) hk)).hom =
    ((Functor.mapIso (X := (modulePullback B S hS (pointHom f)).obj (A.piece i))
          (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g))
          (zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U f).piece i) hi) ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS g
          (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece i) hi)).hom ⊗ₘ
      (Functor.mapIso (X := (modulePullback B S hS (pointHom f)).obj (A.piece j))
          (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g))
          (zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U f).piece j) hj) ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS g
          (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece j) hj)).hom) ≫
      representedTensorChartMul B S hS
        ((quasicoherentPullbackTensorIso B S hS g
            (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece i) hi)
            (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece j) hj)).inv ≫
          quasicoherentPullbackMap B S hS g m) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_map_of_comp_eq B S hS
      (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g) _ _ _ _ _
      (modulePullbackTensorIso_inv_comp_map_mulSheaf_comp_zariskiReadingQuasicoherentIso B S hS A
        U f i j hi hj hk m h))
    (modulePullbackRepresentedQuasicoherentIso_hom_mul_yonedaSpace B S hS g
      (M := zariskiReadingQcoh U ((etalePointAlgebra A U f).piece i) hi)
      (N := zariskiReadingQcoh U ((etalePointAlgebra A U f).piece j) hj)
      (K := zariskiReadingQcoh U ((etalePointAlgebra A U f).piece (i + j)) hk) m)

end PointChart

section ZariskiUnit

/-- **The identification `N ≅ (N_Zar)^a` carries a given unit `e` of a sheaf of graded algebras to
`v`**: for a sheaf of graded algebras `G` on the represented algebraic space of `T` whose piece in
degree `0` is quasi-coherent, a morphism `e : 𝒪 ⟶ G_0` (in practice the unit of `G`, or the
pulled-back unit `𝒪 ≅ u^*𝒪 ⟶ u^*𝒜_0` when `G = u^*𝒜`) and a morphism `v : 𝒪_T ⟶ Z_0` into the
Zariski reading of `G_0` (`AlgebraicGeometry.Space.zariskiReadingQcoh`), `e` followed by
`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso` in degree `0` is the morphism
`𝒪 ≅ (𝒪_T)^a ⟶ Z_0^a` attached to `v` (`AlgebraicGeometry.Space.representedUnitChartHom`). -/
def ZariskiReadingIsoOneCompat (T : BigFppfOver B S hS)
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS (yonedaSpace B S hS T)))
    (h0 : (G.piece 0).IsQuasicoherentOnSite)
    (e : SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)) ⟶ G.piece 0)
    (v : quasicoherentUnitObj B S hS T ⟶ zariskiReadingQcoh T (G.piece 0) h0) : Prop :=
  e ≫ (zariskiReadingQuasicoherentIso T (G.piece 0) h0).hom = representedUnitChartHom B S hS v

/-- **The inverse image along `π_U` of the identification `u^*𝒜_0 ≅ (Z_0)^a`, followed by
`π_U^*(Z_0^a) ≅ (π_U^*Z_0)^a`, is unital**: for a morphism `g : V ⟶ U` of the site, a scheme
point `f : U ⟶ X` and a morphism `v : 𝒪_U ⟶ Z_0` that the identification `f^*𝒜_0 ≅ (Z_0)^a`
carries the pulled-back unit `𝒪 ≅ f^*𝒪 ⟶ f^*𝒜_0` to, the composite
`g^*f^*𝒜_0 ≅ g^*(Z_0^a) ≅ (g^*Z_0)^a` carries the twice pulled-back unit of `𝒜` to the morphism
attached to `𝒪_V ≅ g^*𝒪_U ⟶ g^*Z_0`. -/
theorem modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_one
    {X : AlgebraicSpaces B S hS}
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    {V U : BigFppfOver B S hS} (g : V ⟶ U) (f : yoneda.obj U ⟶ X.1)
    (h0 : ((etalePointAlgebra A U f).piece 0).IsQuasicoherentOnSite)
    (v : quasicoherentUnitObj B S hS U ⟶
      zariskiReadingQcoh U ((etalePointAlgebra A U f).piece 0) h0)
    (h : ZariskiReadingIsoOneCompat B S hS U (etalePointAlgebra A U f) h0
      ((modulePullbackUnitIso B S hS (pointHom f)).inv ≫
        (modulePullback B S hS (pointHom f)).map (SheafOfModules.GradedAlgebra.oneHom A)) v) :
    ((modulePullbackUnitIso B S hS (X := yonedaSpace B S hS U)
        (representedSpaceMap B S hS g)).inv ≫
      (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g)).map
        ((modulePullbackUnitIso B S hS (pointHom f)).inv ≫
          (modulePullback B S hS (pointHom f)).map (SheafOfModules.GradedAlgebra.oneHom A))) ≫
      (Functor.mapIso (X := (modulePullback B S hS (pointHom f)).obj (A.piece 0))
          (modulePullback B S hS (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g))
          (zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U f).piece 0) h0) ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS g
          (zariskiReadingQcoh U ((etalePointAlgebra A U f).piece 0) h0)).hom =
    representedUnitChartHom B S hS
      ((quasicoherentPullbackUnitIso B S hS g).inv ≫ quasicoherentPullbackMap B S hS g v) :=
  unitSquare_comp _ _ _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_map_of_comp_eq B S hS
      (Y := yonedaSpace B S hS U) (representedSpaceMap B S hS g) _ _ _ h)
    (modulePullbackRepresentedQuasicoherentIso_hom_one_yonedaSpace B S hS g
      (K := zariskiReadingQcoh U ((etalePointAlgebra A U f).piece 0) h0) v)

end ZariskiUnit

namespace RelativeProjPoints

section ChartSourceMul

attribute [local irreducible] CategoryTheory.yoneda

variable {B S hS} {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {π : P ⟶ X.obj} (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso` as an explicit composite, with
the represented algebraic space of `U` spelled `AlgebraicGeometry.Space.yonedaSpace` (the
spelling of `AlgebraicGeometry.Space.etalePointAlgebra`). -/
theorem chartPullbackIso_eq_trans_yonedaSpace (n : ℤ) :
    @Eq ((modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
          ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj)
      (d.chartPullbackIso Px hP A hA n)
      (Iso.trans (X := (modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
        isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)))
      ((modulePullbackCompIso B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).app (A.piece n)) ((eqToIso (X :=
                      (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
                          (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X))).obj (A.piece n))
          (Y := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X :=
              (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (yonedaSpace B S hS Px.U))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace))).obj (A.piece n))
          (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n))
            (d.presentationAtlas_comp_homMk Px hP : CategoryStruct.comp
                (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X) (presentationAtlas
              (d.spacePresentation Px hP)) (ObjectProperty.homMk π :
                  (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) = CategoryStruct.comp
                      (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS)) (Y :=
          (yonedaSpace B S hS Px.U))
              (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                  (pointHom Px.toSpace)))) ≪≫ (Iso.symm
            (X := (modulePullback B S hS (Y := yonedaSpace B S hS Px.U)
                (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).obj
              ((modulePullback B S hS (pointHom Px.toSpace)).obj (A.piece n)))
            ((modulePullbackCompIso B S hS
                      (Y := yonedaSpace B S hS Px.U)
                      (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
                          (pointHom Px.toSpace)).app (A.piece n))) ≪≫ ((modulePullback B S hS
                              (Y := yonedaSpace B S hS Px.U)
                              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).mapIso
                                  ((zariskiReadingQuasicoherentIso Px.U
                                      ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) :
              (modulePullback B S hS (X :=
                  (yonedaSpace B S hS Px.U)) (pointHom Px.toSpace)).obj
                          (A.piece n) ≅ _)) ≪≫ modulePullbackRepresentedQuasicoherentIso B S hS
                              (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                                  ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n))) :
        (modulePullback B S hS (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
      isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (presentationAtlas (d.spacePresentation Px hP))).obj ((modulePullback B S hS
              (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n)) ≅
          ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
            (quasicoherentPullbackObj B S hS (d.fibreHom Px.U Px.toSpace) (zariskiReadingQcoh Px.U
                ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)))).obj) :=
  rfl

include d in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_mul`: the
inverse of the composition comparison along `π_U ≫ u`. -/
theorem chartPullbackIso_hom_mul_aux3 (i j : ℤ) :
    type_of% (mulSquare_inv _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (yonedaSpace B S hS Px.U))
        (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace)
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))) :=
  mulSquare_inv _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (yonedaSpace B S hS Px.U))
        (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace)
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))

include d in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_mul`: followed
by the identification of `u^*𝒜_n` with `Z_n^a` and `π_U^*(Z_n^a) ≅ (π_U^*Z_n)^a`. -/
theorem chartPullbackIso_hom_mul_aux34 (i j : ℤ)
    (mZ : quasicoherentTensorObj B S hS Px.U
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece i)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i))
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece j)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)) ⟶
      (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece (i + j))
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j))))
    (hζ : ZariskiReadingIsoMulCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace) i j
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ) :
    type_of% (mulSquare_comp _ _ _ _ _ _ _ _ _
    (chartPullbackIso_hom_mul_aux3 d Px A i j)
    (modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_mul B S hS A
        (d.fibreHom Px.U Px.toSpace) Px.toSpace i j
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ hζ)) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    (chartPullbackIso_hom_mul_aux3 d Px A i j)
    (modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_mul B S hS A
        (d.fibreHom Px.U Px.toSpace) Px.toSpace i j
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ hζ)

include d hP in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_mul`: preceded
by the transport along `c ≫ π = π_U ≫ u`. -/
theorem chartPullbackIso_hom_mul_aux234 (i j : ℤ)
    (mZ : quasicoherentTensorObj B S hS Px.U
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece i)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i))
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece j)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)) ⟶
      (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece (i + j))
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j))))
    (hζ : ZariskiReadingIsoMulCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace) i j
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ) :
    type_of% (mulSquare_comp _ _ _ _ _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_eqToIso B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := X)
        (@id (CategoryStruct.comp
          (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
            isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
          (presentationAtlas (d.spacePresentation Px hP))
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
            CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
                isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
              (Y := yonedaSpace B S hS Px.U) (Z := X)
              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace))
      (d.presentationAtlas_comp_homMk Px hP))
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))
    (chartPullbackIso_hom_mul_aux34 d Px A hA i j mZ hζ)) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_eqToIso B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := X)
        (@id (CategoryStruct.comp
          (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
            isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
          (presentationAtlas (d.spacePresentation Px hP))
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
            CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
                isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
              (Y := yonedaSpace B S hS Px.U) (Z := X)
              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace))
      (d.presentationAtlas_comp_homMk Px hP))
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))
    (chartPullbackIso_hom_mul_aux34 d Px A hA i j mZ hζ)

include d hP in
/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
multiplicative**, for `σ_n` written as the composite of its four factors
(`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_eq_trans_yonedaSpace`). Let `Z_n` be
the Zariski reading of `u^*𝒜_n` on the scheme of `U` and `m : Z_i ⊗ Z_j ⟶ Z_{i+j}` a morphism that
the identification `u^*𝒜_n ≅ (Z_n)^a` carries the multiplication of `u^*𝒜` to
(`AlgebraicGeometry.Space.ZariskiReadingIsoMulCompat`).  Then, with `T` Stacks 03EL,

`(T_c⁻¹ ≫ c^*(T_π⁻¹ ≫ π^*m_𝒜)) ≫ σ_{i+j} = (σ_i ⊗ σ_j) ≫ T_E⁻¹ ≫ E(T_{π_U}⁻¹ ≫ π_U^*m)`,

where `σ_n = (03LU along c ≫ π) ≫ (transport along c ≫ π = π_U ≫ u) ≫ (03LU along π_U ≫ u)⁻¹ ≫
(π_U^*ζ_n ≫ (π_U^*(Z_n^a) ≅ (π_U^*Z_n)^a))`.  The statement is the type of the assembly of its
steps. -/
theorem chartPullbackIso_trans_hom_mul (i j : ℤ)
    (mZ : quasicoherentTensorObj B S hS Px.U
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece i)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i))
        (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece j)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)) ⟶
      (zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece (i + j))
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j))))
    (hζ : ZariskiReadingIsoMulCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace) i j
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace i)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace j)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace (i + j)) mZ) :
    type_of% (mulSquare_comp _ _ _ _ _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
        (presentationAtlas (d.spacePresentation Px hP))
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))
    (chartPullbackIso_hom_mul_aux234 d Px hP A hA i j mZ hζ)) :=
  mulSquare_comp _ _ _ _ _ _ _ _ _
    (modulePullbackTensorIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
        (presentationAtlas (d.spacePresentation Px hP))
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (A.piece i) (A.piece j) (A.piece (i + j))
        ((modulesTensorObjIso B S hS X.1 X.2 (A.piece i) (A.piece j)).hom ≫
          SheafOfModules.GradedAlgebra.mulSheaf A i j))
    (chartPullbackIso_hom_mul_aux234 d Px hP A hA i j mZ hζ)

end ChartSourceMul

section ChartSourceOne

attribute [local irreducible] CategoryTheory.yoneda

variable {B S hS} {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {π : P ⟶ X.obj} (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

include d in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_one`: the
inverse of the composition comparison along `π_U ≫ u`. -/
theorem chartPullbackIso_hom_one_aux3 :
    type_of% (unitSquare_inv _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (yonedaSpace B S hS Px.U))
        (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace)
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))) :=
  unitSquare_inv _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (yonedaSpace B S hS Px.U))
        (Z := X) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace)
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))

include d in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_one`: followed
by the identification of `u^*𝒜_0` with `Z_0^a` and `π_U^*(Z_0^a) ≅ (π_U^*Z_0)^a`. -/
theorem chartPullbackIso_hom_one_aux34
    (vZ : quasicoherentUnitObj B S hS Px.U ⟶
      zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece 0)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0))
    (hζ : ZariskiReadingIsoOneCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0)
      ((modulePullbackUnitIso B S hS (pointHom Px.toSpace)).inv ≫
        (modulePullback B S hS (pointHom Px.toSpace)).map
          (SheafOfModules.GradedAlgebra.oneHom A)) vZ) :
    type_of% (unitSquare_comp _ _ _ _ _
    (chartPullbackIso_hom_one_aux3 d Px A)
    (modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_one B S hS A
        (d.fibreHom Px.U Px.toSpace) Px.toSpace
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0) vZ hζ)) :=
  unitSquare_comp _ _ _ _ _
    (chartPullbackIso_hom_one_aux3 d Px A)
    (modulePullback_mapIso_zariskiReadingQuasicoherentIso_trans_hom_one B S hS A
        (d.fibreHom Px.U Px.toSpace) Px.toSpace
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0) vZ hζ)

include d hP in
/-- Step of `AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_trans_hom_one`: preceded
by the transport along `c ≫ π = π_U ≫ u`. -/
theorem chartPullbackIso_hom_one_aux234
    (vZ : quasicoherentUnitObj B S hS Px.U ⟶
      zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece 0)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0))
    (hζ : ZariskiReadingIsoOneCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0)
      ((modulePullbackUnitIso B S hS (pointHom Px.toSpace)).inv ≫
        (modulePullback B S hS (pointHom Px.toSpace)).map
          (SheafOfModules.GradedAlgebra.oneHom A)) vZ) :
    type_of% (unitSquare_comp _ _ _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_eqToIso B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := X)
        (@id (CategoryStruct.comp
          (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
          (presentationAtlas (d.spacePresentation Px hP))
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
            CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
              (Y := yonedaSpace B S hS Px.U) (Z := X)
              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace))
      (d.presentationAtlas_comp_homMk Px hP))
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))
    (chartPullbackIso_hom_one_aux34 d Px A hA vZ hζ)) :=
  unitSquare_comp _ _ _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_eqToIso B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := X)
        (@id (CategoryStruct.comp
          (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
          (presentationAtlas (d.spacePresentation Px hP))
          (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
            CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
              (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
              (Y := yonedaSpace B S hS Px.U) (Z := X)
              (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace)) (pointHom Px.toSpace))
      (d.presentationAtlas_comp_homMk Px hP))
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))
    (chartPullbackIso_hom_one_aux34 d Px A hA vZ hζ)

include d hP in
/-- **The identification `c^*π^*𝒜_n ≅ (π_U^*Z_n)^a` of the source of `ψ` on the atlas is
unital**, for `σ_0` written as the composite of its four factors
(`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso_eq_trans_yonedaSpace`).  Let `Z_0` be
the Zariski reading of `u^*𝒜_0` on the scheme of `U` and `v : 𝒪_U ⟶ Z_0` a morphism that the
identification `u^*𝒜_0 ≅ (Z_0)^a` carries the pulled-back unit `𝒪 ≅ u^*𝒪 ⟶ u^*𝒜_0` to
(`AlgebraicGeometry.Space.ZariskiReadingIsoOneCompat`).  Then, with `ν_f(w) = (𝒪 ≅ f^*𝒪) ≫ f^*w`
the pulled-back unit (Stacks 03LU),

`ν_c(ν_π(1_𝒜)) ≫ σ_0 = (𝒪 ≅ (𝒪_{P_U})^a) ≫ E(ν_{π_U}(v))`.

The statement is the type of the assembly of its steps. -/
theorem chartPullbackIso_trans_hom_one
    (vZ : quasicoherentUnitObj B S hS Px.U ⟶
      zariskiReadingQcoh Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece 0)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0))
    (hζ : ZariskiReadingIsoOneCompat B S hS Px.U (etalePointAlgebra A Px.U Px.toSpace)
      (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace 0)
      ((modulePullbackUnitIso B S hS (pointHom Px.toSpace)).inv ≫
        (modulePullback B S hS (pointHom Px.toSpace)).map
          (SheafOfModules.GradedAlgebra.oneHom A)) vZ) :
    type_of% (unitSquare_comp _ _ _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
        (presentationAtlas (d.spacePresentation Px hP))
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))
    (chartPullbackIso_hom_one_aux234 d Px hP A hA vZ hζ)) :=
  unitSquare_comp _ _ _ _ _
    (modulePullbackUnitIso_inv_comp_map_comp_modulePullbackCompIso_hom_app B S hS
        (X := (⟨yoneda.obj (d.fibre Px.U Px.toSpace),
          isAlgebraicSpace_yoneda B S hS (d.fibre Px.U Px.toSpace)⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨P, hP⟩ : AlgebraicSpaces B S hS)) (Z := X)
        (presentationAtlas (d.spacePresentation Px hP))
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (A.piece 0) (SheafOfModules.GradedAlgebra.oneHom A))
    (chartPullbackIso_hom_one_aux234 d Px hP A hA vZ hζ)

end ChartSourceOne


end RelativeProjPoints

end AlgebraicGeometry.Space

end
