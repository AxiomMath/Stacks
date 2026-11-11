module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# Cohomology over an object of the big fppf site only sees the objects over it

Let `B` be a big fppf site and `S` a scheme of it. For an object `V` of the big fppf site over
`S`, the cohomology `H^p(V, ℱ)` of an abelian sheaf `ℱ` depends only on the values of `ℱ` on
the objects admitting a morphism to `V`:

* if `ℱ(T) = 0` for every `T` with a morphism `T ⟶ V`, then `H^p(V, ℱ) = 0` for all `p`;
* if `φ : ℱ ⟶ 𝒢` is bijective on sections over every `T` with a morphism `T ⟶ V`, then
  `H^p(V, ℱ) ⟶ H^p(V, 𝒢)` is bijective for all `p`.

The first is the Čech-to-cohomology vanishing criterion
`Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts` for the family of objects
admitting a morphism to `V`, which contains every member of a covering of one of its objects and
every iterated fibre product of such members. The second follows from the first applied to the
kernel and the cokernel of `φ`, through
`Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel`: the kernel
vanishes over such `T` because `φ` is injective there, and the cokernel because it is locally
the image of `𝒢`, which over such `T` is the image of `ℱ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isZero_H'_of_subsingleton_of_hom`: the vanishing statement.
* `AlgebraicGeometry.BigFppfOver.bijective_map_of_bijective_app_of_hom`: the comparison
  statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.BigFppfOver

/-- The vanishing criterion over an object, for a site presented by a pretopology: an abelian
sheaf vanishing on every object with a morphism to `V` has no cohomology over `V`. -/
private theorem isZero_H'_of_subsingleton_of_hom_aux {C : Type*} [Category.{u} C]
    [EssentiallySmall.{u} C] [HasPullbacks C] {J : GrothendieckTopology C} (K : Pretopology C)
    (hK : K.toGrothendieck = J) [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] (F : Sheaf J AddCommGrpCat.{u}) (V : C)
    (hF : ∀ T : C, (T ⟶ V) → Subsingleton (F.obj.obj (op T))) (p : ℕ) :
    IsZero (F.H' p V) := by
  subst hK
  refine Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts K
    {T | Nonempty (T ⟶ V)} F (fun T ⟨g⟩ ↦ ?_) (fun T ⟨g⟩ E _ ↦ ⟨fun i ↦ ⟨E.f i ≫ g⟩,
      fun q s ↦ ?_⟩) V ⟨𝟙 V⟩ p
  · have := hF T g
    exact AddCommGrpCat.isZero_of_subsingleton _
  · let : HasBinaryProducts (Over T) := Over.ConstructProducts.over_binaryProduct_of_pullback
    let : HasFiniteProducts (Over T) := hasFiniteProducts_of_has_binary_and_terminal
    let P := piObj (fun i ↦ Over.mk (E.f (s i)))
    unfold Stacks.CechSite.iteratedFiberProduct
    exact ⟨P.hom ≫ g⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})]

/-- **Cohomology over `V` vanishes for a sheaf vanishing on the objects over `V`.** If an
abelian sheaf `ℱ` on the big fppf site over `S` has `ℱ(T) = 0` for every object `T` admitting a
morphism to `V`, then `H^p(V, ℱ) = 0` for every `p`. -/
public theorem isZero_H'_of_subsingleton_of_hom
    (F : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}) (V : BigFppfOver B S hS)
    (hF : ∀ T : BigFppfOver B S hS, (T ⟶ V) → Subsingleton (F.obj.obj (op T))) (p : ℕ) :
    IsZero (F.H' p V) := by
  let P := Scheme.fppfPrecoverage
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let : P.HasIsos := by
    change Scheme.fppfPrecoverage.HasIsos
    refine ⟨?_⟩
    intro X Y f hf
    have : IsIso f.base := Functor.map_isIso Scheme.forgetToTop f
    have : Surjective f := ⟨(ConcreteCategory.bijective_of_isIso f.base).surjective⟩
    exact f.singleton_mem_fppfPrecoverage
  let : P.IsStableUnderBaseChange := by infer_instance
  let : P.IsStableUnderComposition := by infer_instance
  let : B.precoverage.IsStableUnderBaseChange := by
    rw [bigFppf_precoverage_eq B]
    infer_instance
  let K : Pretopology (AlgebraicGeometry.BigFppfOver B S hS) := (P.comap G).toPretopology
  have hpre : P.comap G =
      (B.precoverage.comap (AlgebraicGeometry.BigFppfOver.forget B S hS)) := by
    calc
      P.comap G = (P.comap B.inclusion).comap
          (AlgebraicGeometry.BigFppfOver.forget B S hS) := by
        rw [Precoverage.comap_comp]
      _ = B.precoverage.comap (AlgebraicGeometry.BigFppfOver.forget B S hS) :=
        congrArg (fun J : Precoverage B.Schemes ↦
          J.comap (AlgebraicGeometry.BigFppfOver.forget B S hS))
          (bigFppf_precoverage_eq B).symm
  have hK : K.toGrothendieck = AlgebraicGeometry.BigFppfOver.topology B S hS := by
    calc
      K.toGrothendieck = (P.comap G).toGrothendieck := by
        dsimp [K]
        exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck
      _ = (B.precoverage.comap
          (AlgebraicGeometry.BigFppfOver.forget B S hS)).toGrothendieck := by rw [hpre]
      _ = B.topology.over (B.obj hS) := by
        rw [← CategoryTheory.over_toGrothendieck_eq_toGrothendieck_comap_forget]
      _ = AlgebraicGeometry.BigFppfOver.topology B S hS := rfl
  let : EssentiallySmall.{u} B.Schemes := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj hS)
  exact isZero_H'_of_subsingleton_of_hom_aux K hK F V hF p

omit [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})] in
/-- The kernel of a morphism of abelian sheaves vanishes over an object on whose sections the
morphism is injective. -/
public theorem subsingleton_kernel_obj
    {F G : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}} (φ : F ⟶ G)
    (T : BigFppfOver B S hS) (hφ : Function.Injective (φ.hom.app (op T))) :
    Subsingleton ((kernel φ).obj.obj (op T)) := by
  have hmono : Mono ((kernel.ι φ).hom.app (op T)) := by
    have : Mono ((sheafToPresheaf _ _).map (kernel.ι φ)) := inferInstance
    exact (inferInstance : Mono (((sheafToPresheaf _ _).map (kernel.ι φ)).app (op T)))
  have hinj := (AddCommGrpCat.mono_iff_injective _).mp hmono
  have hc : ∀ x, φ.hom.app (op T) ((kernel.ι φ).hom.app (op T) x) = 0 := fun x ↦
    congrArg (fun f : kernel φ ⟶ G ↦ f.hom.app (op T) x) (kernel.condition φ)
  have hx : ∀ x, (kernel.ι φ).hom.app (op T) x = 0 := fun x ↦ hφ ((hc x).trans (map_zero _).symm)
  exact ⟨fun x y ↦ hinj ((hx x).trans (hx y).symm)⟩

omit [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})] in
/-- The cokernel of a morphism of abelian sheaves vanishes over an object `T` such that the
morphism is locally surjective over every object mapping to `T`: every section of the target
over such an object lifts on a covering of it. -/
public theorem subsingleton_cokernel_obj
    {F G : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}} (φ : F ⟶ G)
    (T : BigFppfOver B S hS)
    (hφ : ∀ ⦃Y : BigFppfOver B S hS⦄ (_ : Y ⟶ T) (g : G.obj.obj (op Y)),
      ∃ R ∈ BigFppfOver.topology B S hS Y, ∀ ⦃Y' : BigFppfOver B S hS⦄ (h : Y' ⟶ Y), R h →
        ∃ r : F.obj.obj (op Y'), φ.hom.app (op Y') r = G.obj.map h.op g) :
    Subsingleton ((cokernel φ).obj.obj (op T)) := by
  let : EssentiallySmall.{u} B.Schemes := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  let : EssentiallySmall.{u} (AlgebraicGeometry.BigFppfOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj hS)
  have := wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{u}
    (BigFppfOver.topology B S hS)
  have := hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall.{u}
    (BigFppfOver.topology B S hS)
  have hepi : Sheaf.IsLocallySurjective (cokernel.π φ) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π φ)).mpr inferInstance
  have hsep : Presheaf.IsSeparated (BigFppfOver.topology B S hS) (cokernel φ).obj :=
    Sheaf.isSeparated (cokernel φ)
  have hc : ∀ (Y : BigFppfOver B S hS) (r : F.obj.obj (op Y)),
      (cokernel.π φ).hom.app (op Y) (φ.hom.app (op Y) r) = 0 := fun Y r ↦
    congrArg (fun h : F ⟶ cokernel φ ↦ h.hom.app (op Y) r) (cokernel.condition φ)
  have hzero : ∀ z : (cokernel φ).obj.obj (op T), z = 0 := by
    intro z
    have hmem : Presheaf.imageSieve (cokernel.π φ).hom z ∈ BigFppfOver.topology B S hS T :=
      Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) (cokernel.π φ).hom z
    refine hsep T _ hmem z 0 (fun Y f hf ↦ ?_)
    obtain ⟨t, ht⟩ := hf
    rw [map_zero, ← ht]
    obtain ⟨R, hR, hRl⟩ := hφ f t
    refine hsep Y R hR _ 0 (fun Y' h hh ↦ ?_)
    obtain ⟨r, hr⟩ := hRl h hh
    have hnat := ConcreteCategory.congr_hom ((cokernel.π φ).hom.naturality h.op) t
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    rw [map_zero, ← hnat, ← hr, hc]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

/-- **A morphism of abelian sheaves bijective over the objects over `V` is bijective on
cohomology over `V`.** If `φ : ℱ ⟶ 𝒢` is bijective on sections over every object `T` admitting a
morphism to `V`, then `H^n(V, ℱ) ⟶ H^n(V, 𝒢)` is bijective for every `n`. -/
public theorem bijective_map_of_bijective_app_of_hom
    {F G : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u}} (φ : F ⟶ G)
    (V : BigFppfOver B S hS)
    (hφ : ∀ T : BigFppfOver B S hS, (T ⟶ V) → Function.Bijective (φ.hom.app (op T)))
    (n : ℕ) :
    Function.Bijective (Stacks.Cohomology.LongExactSequence.map.{w} φ n V) :=
  Stacks.Cohomology.LongExactSequence.bijective_map_of_subsingleton_kernel_cokernel φ V
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero
      (isZero_H'_of_subsingleton_of_hom B S hS _ V
        (fun T g ↦ subsingleton_kernel_obj B S hS φ T (hφ T g).1) q))
    (fun q ↦ AddCommGrpCat.subsingleton_of_isZero
      (isZero_H'_of_subsingleton_of_hom B S hS _ V
        (fun T g ↦ subsingleton_cokernel_obj B S hS φ T
          (fun Y f _ ↦ ⟨⊤, (BigFppfOver.topology B S hS).top_mem Y, fun Y' h _ ↦
            (hφ Y' (h ≫ f ≫ g)).2 _⟩)) q)) n

end AlgebraicGeometry.BigFppfOver

end
