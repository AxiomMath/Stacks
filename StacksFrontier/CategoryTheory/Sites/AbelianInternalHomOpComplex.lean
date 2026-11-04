module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpModule

/-!
# The internal Hom complex of a complex of sheaves of `Λ`-modules into a complex of abelian sheaves

Let `(C, K)` be a site, `Λ` a ring, `L` a complex of sheaves of `Λ`-modules and `M` a complex of
abelian sheaves. The internal Hom complex `ℋom^•_ℤ(L, M)` has in degree `n` the product, over
the pairs `(p, q)` with `p + n = q`, of the abelian internal Hom sheaves `ℋom_ℤ(L^p, M^q)`, each a
sheaf of `Λᵐᵒᵖ`-modules through the action of `Λ` on `L^p`
(`Stacks.AbelianInternalHom.homOpSheaf`); the differential is the Hom-complex differential
`δ z = z ≫ d_M + (-1)^{n+1} d_L ≫ z` of Mathlib's `CochainComplex.HomComplex.δ`
(`Stacks.AbelianInternalHom.homOpComplex`). It is contravariant in `L` by precomposition
(`Stacks.AbelianInternalHom.homOpComplexPrecomp`).

This is the complex of sheaves whose Galois-equivariant global sections compute
`RHom(ℱ, μ_n)` in the derived Poincaré duality of Tag 03VM; the pairing with `L` is evaluation.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MulOpposite Stacks.ModuleCatLift

universe w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]

section Laws

/-- Morphisms between sheaves of `Λᵐᵒᵖ`-modules are determined by their underlying morphisms of
abelian sheaves. -/
lemma homOp_hom_ext {X Y : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)} {f g : X ⟶ Y}
    (h : (sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ) AddCommGrpCat.{max u v})).map f =
      (sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ) AddCommGrpCat.{max u v})).map g) :
    f = g :=
  (sheafCompose K (forget₂ (ModuleCat.{max u v} Λᵐᵒᵖ) AddCommGrpCat.{max u v})).map_injective h

variable (G : Sheaf K (ModuleCat.{max u v} Λ))

/-- Postcomposition `ℋom_ℤ(G, F) ⟶ ℋom_ℤ(G, F')` is compatible with composition. -/
lemma homOpMap_comp {F F' F'' : Sheaf K AddCommGrpCat.{max u v}} (g : F ⟶ F') (g' : F' ⟶ F'') :
    homOpMap K G g ≫ homOpMap K G g' = homOpMap K G (g ≫ g') :=
  ((homOpFunctor K G).map_comp g g').symm

/-- Postcomposition with the zero morphism is zero. -/
lemma homOpMap_zero (F F' : Sheaf K AddCommGrpCat.{max u v}) :
    homOpMap K G (0 : F ⟶ F') = 0 := by
  refine homOp_hom_ext K (Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun x => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun y => ?_))))))
  rfl

/-- Precomposition is contravariantly compatible with composition: precomposing with `ψ` and
then with `φ` is precomposing with `φ ≫ ψ`. -/
lemma homOpMapLeft_comp {G₁ G₂ G₃ : Sheaf K (ModuleCat.{max u v} Λ)} (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    homOpMapLeft K ψ F ≫ homOpMapLeft K φ F = homOpMapLeft K (φ ≫ ψ) F := by
  refine homOp_hom_ext K ?_
  show (internalHomFunctor K F).map _ ≫ (internalHomFunctor K F).map _ =
    (internalHomFunctor K F).map _
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp]

/-- Precomposition with the identity of `G` is the identity of `ℋom_ℤ(G, F)`. -/
lemma homOpMapLeft_id (F : Sheaf K AddCommGrpCat.{max u v}) :
    homOpMapLeft K (𝟙 G) F = 𝟙 _ := by
  refine homOp_hom_ext K ?_
  show (internalHomFunctor K F).map _ = 𝟙 _
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]

/-- Precomposition with the zero morphism is zero. -/
lemma homOpMapLeft_zero {G₁ G₂ : Sheaf K (ModuleCat.{max u v} Λ)}
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    homOpMapLeft K (0 : G₁ ⟶ G₂) F = 0 := by
  refine homOp_hom_ext K (Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun x => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun y => ?_))))))
  exact map_zero (x.app W).hom

/-- Precomposition is additive in the morphism precomposed with. -/
lemma homOpMapLeft_add {G₁ G₂ : Sheaf K (ModuleCat.{max u v} Λ)} (φ ψ : G₁ ⟶ G₂)
    (F : Sheaf K AddCommGrpCat.{max u v}) :
    homOpMapLeft K (φ + ψ) F = homOpMapLeft K φ F + homOpMapLeft K ψ F := by
  refine homOp_hom_ext K (Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun x => NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun y => ?_))))))
  exact map_add (x.app W).hom _ _

/-- Precomposition with `φ : G₁ ⟶ G₂` commutes with postcomposition with `g : F ⟶ F'`. -/
lemma homOpMapLeft_homOpMap {G₁ G₂ : Sheaf K (ModuleCat.{max u v} Λ)} (φ : G₁ ⟶ G₂)
    {F F' : Sheaf K AddCommGrpCat.{max u v}} (g : F ⟶ F') :
    homOpMapLeft K φ F ≫ homOpMap K G₁ g = homOpMap K G₂ g ≫ homOpMapLeft K φ F' := by
  refine homOp_hom_ext K (Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun x => ?_))))
  rfl

end Laws

section Complex

variable (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ)
  (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ)

/-- The pairs `(p, q)` with `p + n = q`, indexing the factors of `ℋom^n_ℤ(L, M)`. -/
abbrev HomOpIndex (n : ℤ) : Type := {pq : ℤ × ℤ // pq.1 + n = pq.2}

/-- The degree-`n` term `∏_{p + n = q} ℋom_ℤ(L^p, M^q)` of the internal Hom complex. -/
def homOpComplexX (n : ℤ) : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ) :=
  ∏ᶜ fun x : HomOpIndex n => homOpSheaf K (L.X x.1.1) (M.X x.1.2)

/-- The projection of `ℋom^n_ℤ(L, M)` onto the factor `ℋom_ℤ(L^p, M^q)`. -/
def homOpComplexπ (n : ℤ) (x : HomOpIndex n) :
    homOpComplexX K L M n ⟶ homOpSheaf K (L.X x.1.1) (M.X x.1.2) :=
  Pi.π (fun x : HomOpIndex n => homOpSheaf K (L.X x.1.1) (M.X x.1.2)) x

/-- A morphism into `ℋom^n_ℤ(L, M)` from its components. -/
def homOpComplexLift {Y : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)} (n : ℤ)
    (φ : ∀ x : HomOpIndex n, Y ⟶ homOpSheaf K (L.X x.1.1) (M.X x.1.2)) :
    Y ⟶ homOpComplexX K L M n :=
  Pi.lift φ

/-- The components of `homOpComplexLift K L M n φ` are the morphisms `φ x`. -/
@[reassoc (attr := simp)]
lemma homOpComplexLift_π {Y : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)} (n : ℤ)
    (φ : ∀ x : HomOpIndex n, Y ⟶ homOpSheaf K (L.X x.1.1) (M.X x.1.2)) (x : HomOpIndex n) :
    homOpComplexLift K L M n φ ≫ homOpComplexπ K L M n x = φ x :=
  Pi.lift_π _ _

/-- Two morphisms into `ℋom^n_ℤ(L, M)` agree if all their components agree. -/
lemma homOpComplexX_hom_ext {Y : Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)} (n : ℤ)
    {f g : Y ⟶ homOpComplexX K L M n}
    (h : ∀ x, f ≫ homOpComplexπ K L M n x = g ≫ homOpComplexπ K L M n x) : f = g :=
  Pi.hom_ext _ _ h

/-- The component of the differential `ℋom^n_ℤ(L, M) ⟶ ℋom_ℤ(L^p, M^q)`, `p + n + 1 = q`:
`z ↦ z ≫ d_M + (-1)^{n+1} d_L ≫ z`. -/
def homOpComplexDComponent (n : ℤ) (x : HomOpIndex (n + 1)) :
    homOpComplexX K L M n ⟶ homOpSheaf K (L.X x.1.1) (M.X x.1.2) :=
  homOpComplexπ K L M n (⟨(x.1.1, x.1.2 - 1), by have := x.2; omega⟩ : HomOpIndex n) ≫
      homOpMap K (L.X x.1.1) (M.d (x.1.2 - 1) x.1.2) +
    (n + 1).negOnePow •
      (homOpComplexπ K L M n (⟨(x.1.1 + 1, x.1.2), by have := x.2; omega⟩ : HomOpIndex n) ≫
        homOpMapLeft K (L.d x.1.1 (x.1.1 + 1)) (M.X x.1.2))

/-- The differential of the internal Hom complex. -/
def homOpComplexD (n : ℤ) : homOpComplexX K L M n ⟶ homOpComplexX K L M (n + 1) :=
  homOpComplexLift K L M (n + 1) (homOpComplexDComponent K L M n)

/-- The components of the differential `homOpComplexD` are the morphisms
`homOpComplexDComponent`. -/
@[reassoc (attr := simp)]
lemma homOpComplexD_π (n : ℤ) (x : HomOpIndex (n + 1)) :
    homOpComplexD K L M n ≫ homOpComplexπ K L M (n + 1) x = homOpComplexDComponent K L M n x :=
  homOpComplexLift_π _ _ _ _ _ _

/-- The differential of the internal Hom complex squares to zero. -/
lemma homOpComplexD_comp_d (n : ℤ) :
    homOpComplexD K L M n ≫ homOpComplexD K L M (n + 1) = 0 := by
  refine homOpComplexX_hom_ext K L M _ fun x => ?_
  simp only [Category.assoc, homOpComplexD_π, zero_comp]
  unfold homOpComplexDComponent
  simp only [Preadditive.comp_add, Linear.comp_units_smul, homOpComplexD_π_assoc]
  unfold homOpComplexDComponent
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, homOpMap_comp,
    homOpMapLeft_comp, HomologicalComplex.d_comp_d, homOpMap_zero, homOpMapLeft_zero, comp_zero,
    smul_zero, zero_add, add_zero, homOpMapLeft_homOpMap]
  rw [show (n + 1 + 1).negOnePow = -(n + 1).negOnePow from Int.negOnePow_succ (n + 1)]
  rw [Units.neg_smul]
  abel

/-- **The internal Hom complex** `ℋom^•_ℤ(L, M)`, a complex of sheaves of `Λᵐᵒᵖ`-modules. -/
def homOpComplex : CochainComplex (Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)) ℤ :=
  CochainComplex.of (homOpComplexX K L M) (homOpComplexD K L M) (homOpComplexD_comp_d K L M)

/-- The degree-`n` term of `ℋom^•_ℤ(L, M)` is `homOpComplexX K L M n`. -/
@[simp]
lemma homOpComplex_X (n : ℤ) : (homOpComplex K L M).X n = homOpComplexX K L M n := rfl

/-- The differential of `ℋom^•_ℤ(L, M)` from degree `n` to `n + 1` is `homOpComplexD K L M n`. -/
@[simp]
lemma homOpComplex_d (n : ℤ) : (homOpComplex K L M).d n (n + 1) = homOpComplexD K L M n :=
  CochainComplex.of_d _ _ n

variable {K L M} in
/-- The degree-`n` component of precomposition with `f : L' ⟶ L`. -/
def homOpComplexPrecompX {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ} (f : L' ⟶ L)
    (n : ℤ) : homOpComplexX K L M n ⟶ homOpComplexX K L' M n :=
  homOpComplexLift K L' M n fun x =>
    homOpComplexπ K L M n x ≫ homOpMapLeft K (f.f x.1.1) (M.X x.1.2)

/-- The `(p, q)`-component of `homOpComplexPrecompX f n` is precomposition with
`f.f p : L'^p ⟶ L^p`. -/
@[reassoc (attr := simp)]
lemma homOpComplexPrecompX_π {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f : L' ⟶ L) (n : ℤ) (x : HomOpIndex n) :
    homOpComplexPrecompX (M := M) f n ≫ homOpComplexπ K L' M n x =
      homOpComplexπ K L M n x ≫ homOpMapLeft K (f.f x.1.1) (M.X x.1.2) :=
  homOpComplexLift_π _ _ _ _ _ _

variable {K L M} in
/-- **Precomposition** `ℋom^•_ℤ(L, M) ⟶ ℋom^•_ℤ(L', M)` with a morphism of complexes
`f : L' ⟶ L`. -/
def homOpComplexPrecomp {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ} (f : L' ⟶ L) :
    homOpComplex K L M ⟶ homOpComplex K L' M :=
  CochainComplex.ofHom (X := homOpComplex K L M) (Y := homOpComplex K L' M)
    (homOpComplexPrecompX (M := M) f) (fun n => by
    rw [homOpComplex_d, homOpComplex_d]
    refine homOpComplexX_hom_ext K L' M _ fun x => ?_
    change (homOpComplexPrecompX (M := M) f n ≫ homOpComplexD K L' M n) ≫
        homOpComplexπ K L' M (n + 1) x =
      (homOpComplexD K L M n ≫ homOpComplexPrecompX (M := M) f (n + 1)) ≫
        homOpComplexπ K L' M (n + 1) x
    simp only [Category.assoc, homOpComplexD_π, homOpComplexD_π_assoc, homOpComplexPrecompX_π]
    unfold homOpComplexDComponent
    simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
      Linear.units_smul_comp, Category.assoc, homOpComplexPrecompX_π_assoc, homOpMapLeft_homOpMap,
      homOpMapLeft_comp, HomologicalComplex.Hom.comm])

/-- The degree-`n` component of `homOpComplexPrecomp f` is `homOpComplexPrecompX f n`. -/
@[simp]
lemma homOpComplexPrecomp_f {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f : L' ⟶ L) (n : ℤ) :
    (homOpComplexPrecomp (M := M) f).f n = homOpComplexPrecompX (M := M) f n := rfl

/-- Precomposition with the identity of `L` is the identity of `ℋom^•_ℤ(L, M)`. -/
lemma homOpComplexPrecomp_id : homOpComplexPrecomp (M := M) (𝟙 L) = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => homOpComplexX_hom_ext K L M _ fun x => ?_
  show homOpComplexPrecompX (M := M) (𝟙 L) n ≫ homOpComplexπ K L M n x =
    𝟙 (homOpComplexX K L M n) ≫ homOpComplexπ K L M n x
  simp only [homOpComplexPrecompX_π, HomologicalComplex.id_f,
    homOpMapLeft_id, Category.comp_id, Category.id_comp]

/-- Precomposition is contravariantly compatible with composition: precomposing with `f` and
then with `g` is precomposing with `g ≫ f`. -/
lemma homOpComplexPrecomp_comp {L' L'' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f : L' ⟶ L) (g : L'' ⟶ L') :
    homOpComplexPrecomp (M := M) f ≫ homOpComplexPrecomp (M := M) g =
      homOpComplexPrecomp (M := M) (g ≫ f) := by
  refine HomologicalComplex.hom_ext _ _ fun n => homOpComplexX_hom_ext K L'' M _ fun x => ?_
  show (homOpComplexPrecompX (M := M) f n ≫ homOpComplexPrecompX (M := M) g n) ≫
      homOpComplexπ K L'' M n x =
        homOpComplexPrecompX (M := M) (g ≫ f) n ≫ homOpComplexπ K L'' M n x
  simp only [Category.assoc, homOpComplexPrecompX_π, homOpComplexPrecompX_π_assoc,
    homOpMapLeft_comp, HomologicalComplex.comp_f]

/-- Precomposition of internal Hom complexes is additive in the morphism of complexes. -/
lemma homOpComplexPrecomp_add {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ}
    (f g : L' ⟶ L) :
    homOpComplexPrecomp (M := M) (f + g) =
      homOpComplexPrecomp (M := M) f + homOpComplexPrecomp (M := M) g := by
  refine HomologicalComplex.hom_ext _ _ fun n => homOpComplexX_hom_ext K L' M _ fun x => ?_
  show homOpComplexPrecompX (M := M) (f + g) n ≫ homOpComplexπ K L' M n x =
    (homOpComplexPrecompX (M := M) f n + homOpComplexPrecompX (M := M) g n) ≫
      homOpComplexπ K L' M n x
  simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp,
    homOpComplexPrecompX_π, homOpMapLeft_add, Preadditive.comp_add]

/-- Precomposition with the zero morphism of complexes is zero. -/
lemma homOpComplexPrecomp_zero {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ} :
    homOpComplexPrecomp (M := M) (0 : L' ⟶ L) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => homOpComplexX_hom_ext K L' M _ fun x => ?_
  show homOpComplexPrecompX (M := M) (0 : L' ⟶ L) n ≫ homOpComplexπ K L' M n x =
    (0 : homOpComplexX K L M n ⟶ homOpComplexX K L' M n) ≫ homOpComplexπ K L' M n x
  simp only [HomologicalComplex.zero_f, zero_comp, homOpComplexPrecompX_π, homOpMapLeft_zero,
    comp_zero]

variable {K M} in
/-- The short complex `ℋom^•(L₃, M) ⟶ ℋom^•(L₂, M) ⟶ ℋom^•(L₁, M)` of precompositions attached
to a short complex `L₁ ⟶ L₂ ⟶ L₃`. -/
def homOpComplexPrecompShortComplex
    (S : ShortComplex (CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ)) :
    ShortComplex (CochainComplex (Sheaf K (ModuleCat.{max u v} Λᵐᵒᵖ)) ℤ) :=
  ShortComplex.mk (homOpComplexPrecomp (M := M) S.g) (homOpComplexPrecomp (M := M) S.f) (by
    rw [homOpComplexPrecomp_comp, S.zero, homOpComplexPrecomp_zero])

variable {K M} in
/-- **A degreewise split short complex of `L`'s gives a degreewise split short complex of
internal Hom complexes.** -/
theorem homOpComplexPrecompShortComplex_splitting
    (S : ShortComplex (CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ))
    (h : ∀ p, Nonempty ((S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) p)).Splitting))
    (n : ℤ) :
    Nonempty (((homOpComplexPrecompShortComplex (M := M) S).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting) := by
  let σ := fun p => (h p).some
  have hfr : ∀ p, S.f.f p ≫ (σ p).r = 𝟙 (S.X₁.X p) := fun p => (σ p).f_r
  have hsg : ∀ p, (σ p).s ≫ S.g.f p = 𝟙 (S.X₃.X p) := fun p => (σ p).s_g
  have hid : ∀ p, ((σ p).r ≫ S.f.f p : S.X₂.X p ⟶ S.X₂.X p) +
      (S.g.f p ≫ (σ p).s : S.X₂.X p ⟶ S.X₂.X p) = 𝟙 (S.X₂.X p) := fun p => (σ p).id
  refine ⟨{
    r := homOpComplexLift K S.X₃ M n fun x =>
      homOpComplexπ K S.X₂ M n x ≫ homOpMapLeft K (σ x.1.1).s (M.X x.1.2)
    s := homOpComplexLift K S.X₂ M n fun x =>
      homOpComplexπ K S.X₁ M n x ≫ homOpMapLeft K (σ x.1.1).r (M.X x.1.2)
    f_r := ?_
    s_g := ?_
    id := ?_ }⟩
  · show homOpComplexPrecompX (M := M) S.g n ≫ (homOpComplexLift K S.X₃ M n fun x =>
      homOpComplexπ K S.X₂ M n x ≫ homOpMapLeft K (σ x.1.1).s (M.X x.1.2)) =
        𝟙 (homOpComplexX K S.X₃ M n)
    refine homOpComplexX_hom_ext K S.X₃ M n fun x => ?_
    simp only [Category.assoc, homOpComplexLift_π, homOpComplexPrecompX_π_assoc,
      homOpMapLeft_comp, Category.id_comp, hsg]
    exact Category.comp_id _
  · show (homOpComplexLift K S.X₂ M n fun x =>
      homOpComplexπ K S.X₁ M n x ≫ homOpMapLeft K (σ x.1.1).r (M.X x.1.2)) ≫
        homOpComplexPrecompX (M := M) S.f n = 𝟙 (homOpComplexX K S.X₁ M n)
    refine homOpComplexX_hom_ext K S.X₁ M n fun x => ?_
    simp only [Category.assoc, homOpComplexPrecompX_π,
      homOpComplexLift_π_assoc, homOpMapLeft_comp, Category.id_comp, hfr, homOpMapLeft_id]
    exact Category.comp_id _
  · show (homOpComplexLift K S.X₃ M n fun x =>
      homOpComplexπ K S.X₂ M n x ≫ homOpMapLeft K (σ x.1.1).s (M.X x.1.2)) ≫
        homOpComplexPrecompX (M := M) S.g n + homOpComplexPrecompX (M := M) S.f n ≫
          (homOpComplexLift K S.X₂ M n fun x =>
            homOpComplexπ K S.X₁ M n x ≫ homOpMapLeft K (σ x.1.1).r (M.X x.1.2)) =
        𝟙 (homOpComplexX K S.X₂ M n)
    refine homOpComplexX_hom_ext K S.X₂ M n fun x => ?_
    simp only [Preadditive.add_comp, Category.assoc, homOpComplexLift_π, homOpComplexPrecompX_π,
      homOpComplexLift_π_assoc, homOpComplexPrecompX_π_assoc, homOpMapLeft_comp, Category.id_comp,
      ← Preadditive.comp_add, ← homOpMapLeft_add]
    rw [add_comm, hid, homOpMapLeft_id]
    exact Category.comp_id _

end Complex

end Stacks.AbelianInternalHom

end
